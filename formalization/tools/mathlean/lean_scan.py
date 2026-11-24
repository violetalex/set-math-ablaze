"""Lean 源码静态检查。

三件事：
  * `strip_comments`  —— 去掉注释（保留换行，行号不变）；
  * `scan_tokens`     —— 扫 sorry / admit 这类占位符；
  * `declarations`    —— 抽出 theorem / lemma / axiom 的全名（含 namespace 前缀）。

不做语法分析，够用即可；真正的合法性由 `lake build` 判定。
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

# 这些构造都会让 kernel 之外的东西参与判定，和一个洞一样需要显式审计：
#   sorry / admit        —— 接受任意命题，直接留洞；
#   native_decide        —— 把判定编译成本机代码，信任编译器；
#   implemented_by       —— 运行时替换实现，逻辑值与实际执行不一致；
#   extern               —— 声明一个 Lean 之外实现的常量。
DEFAULT_TOKENS = ("sorry", "admit", "native_decide", "implemented_by", "extern")

_DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|"
    r"partial[ \t]+|unsafe[ \t]+|scoped[ \t]+)*"
    r"(theorem|lemma|axiom)[ \t]+([^\s({\[:]+)",
    re.M,
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)", re.M)
_SECTION_RE = re.compile(r"^\s*section(?:\s+([^\s]+))?\s*$", re.M)
_END_RE = re.compile(r"^\s*end(?:\s+([^\s]+))?\s*$", re.M)


def strip_comments(src: str) -> str:
    """去掉 `--` 行注释与可嵌套的 `/- ... -/` 块注释，保留换行。

    同时跳过双引号字符串，避免把字符串里的 `--` 当成注释。
    """
    out: List[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        ch = src[i]
        if depth == 0 and not in_str and src.startswith("/-", i):
            depth, i = 1, i + 2
            continue
        if depth > 0:
            if src.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif src.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(src[i + 1])
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
            out.append(ch)
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(ch)
        i += 1
    return "".join(out)


@dataclass
class Finding:
    path: str
    line: int
    token: str
    text: str = ""

    def __str__(self) -> str:
        return "{}:{}: {}".format(self.path, self.line, self.token)


@dataclass
class Decl:
    name: str
    short: str
    kind: str
    path: str
    line: int


def _line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def scan_text(text: str, path: str = "<text>",
              tokens: Sequence[str] = DEFAULT_TOKENS) -> List[Finding]:
    code = strip_comments(text)
    found: List[Finding] = []
    for tok in tokens:
        for m in re.finditer(r"\b" + re.escape(tok) + r"\b", code):
            line = _line_of(code, m.start())
            src_line = text.splitlines()[line - 1] if line - 1 < len(text.splitlines()) else ""
            found.append(Finding(path, line, tok, src_line.strip()))
    found.sort(key=lambda f: (f.line, f.token))
    return found


def scan_files(paths: Iterable[Path], root: Optional[Path] = None,
               tokens: Sequence[str] = DEFAULT_TOKENS) -> Tuple[List[Finding], int]:
    """返回 (findings, 扫描文件数)。"""
    findings: List[Finding] = []
    count = 0
    for p in paths:
        count += 1
        rel = str(p.relative_to(root)) if root else str(p)
        findings.extend(scan_text(p.read_text(encoding="utf-8", errors="replace"), rel, tokens))
    return findings, count


def declarations(text: str, path: str = "<text>") -> List[Decl]:
    """抽出声明，并把 `namespace Foo` 前缀补上。"""
    code = strip_comments(text)
    lines = code.splitlines()
    stack: List[Tuple[str, Optional[str]]] = []  # ("namespace"|"section", name)
    out: List[Decl] = []

    def prefix() -> str:
        return ".".join(n for kind, n in stack if kind == "namespace" and n)

    for idx, line in enumerate(lines, start=1):
        m = _NAMESPACE_RE.match(line)
        if m:
            stack.append(("namespace", m.group(1)))
            continue
        m = _SECTION_RE.match(line)
        if m:
            stack.append(("section", m.group(1)))
            continue
        m = _END_RE.match(line)
        if m:
            name = m.group(1)
            if name:
                # `end Foo`：弹到匹配的 namespace/section 为止
                while stack:
                    kind, n = stack.pop()
                    if n == name or (kind == "namespace" and n.split(".")[-1] == name):
                        break
            elif stack:
                stack.pop()
            continue
        m = _DECL_RE.match(line)
        if m:
            kind, short = m.group(1), m.group(2)
            full = (prefix() + "." + short) if prefix() else short
            out.append(Decl(full, short, kind, path, idx))
    return out


def parse_lean_file(path: Path, root: Optional[Path] = None) -> List[Decl]:
    rel = str(path.relative_to(root)) if root else str(path)
    return declarations(path.read_text(encoding="utf-8", errors="replace"), rel)


def library_sources(root: Path, lib: str) -> List[Path]:
    """工程里属于本库的 .lean 文件（排除 .lake、Audit.lean、tools）。"""
    files: List[Path] = []
    lib_dir = root / lib
    if lib_dir.is_dir():
        files.extend(sorted(p for p in lib_dir.rglob("*.lean")))
    top = root / (lib + ".lean")
    if top.is_file():
        files.append(top)
    return [p for p in files if ".lake" not in p.parts]


def infer_lib(root: Path) -> str:
    """猜库名：优先 `[[lean_lib]]` 的 name，其次唯一的 .lean 子目录。"""
    toml = root / "lakefile.toml"
    if toml.is_file():
        text = toml.read_text(encoding="utf-8", errors="replace")
        block = re.search(r"\[\[lean_lib\]\](.*?)(?=\n\[\[|\Z)", text, re.S)
        if block:
            m = re.search(r'name\s*=\s*"([^"]+)"', block.group(1))
            if m:
                return m.group(1)
    leanfile = root / "lakefile.lean"
    if leanfile.is_file():
        text = leanfile.read_text(encoding="utf-8", errors="replace")
        m = re.search(r"lean_lib\s+`?([A-Za-z0-9_]+)", text) or \
            re.search(r'name\s*:=\s*"([^"]+)"', text)
        if m:
            return m.group(1)
    candidates = [d for d in root.iterdir()
                  if d.is_dir() and d.name not in (".lake", "tools", "docs", "scripts")
                  and any(d.glob("*.lean"))]
    if len(candidates) == 1:
        return candidates[0].name
    return ""
