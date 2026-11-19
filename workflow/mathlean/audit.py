"""公理审计：跑 `lake env lean Audit.lean`，解析每个声明依赖的公理。

Lean 的输出形如：

    'Foo.bar' depends on axioms: [propext, Classical.choice]
    'Foo.baz' does not depend on any axioms

不解析 `lake build` 的警告——那条路会漏掉 `axiom` 声明和 `sorryAx` 的组合。
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

_DEPENDS = re.compile(r"^'?([^\s']+)'?\s+depends on axioms:\s*\[(.*?)\]\s*$")
_NO_AXIOM = re.compile(r"^'?([^\s']+)'?\s+does not depend on any axioms\s*$")
_AXIOM_DECL = re.compile(
    r"^[ \t]*(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+)*axiom[ \t]+([^\s({\[:]+)",
    re.M,
)
_PRINT_AXIOMS = re.compile(r"#print\s+axioms\s+([^\s]+)")


def elan_bin() -> Optional[Path]:
    p = Path.home() / ".elan" / "bin"
    return p if (p / "lake").exists() else None


def lean_env() -> Dict[str, str]:
    env = dict(os.environ)
    bin_dir = elan_bin()
    if bin_dir:
        env["PATH"] = str(bin_dir) + os.pathsep + env.get("PATH", "")
    return env


def parse_axioms(output: str) -> Dict[str, Set[str]]:
    """从 Lean 输出里抽 {声明全名: 公理集合}。"""
    result: Dict[str, Set[str]] = {}
    for raw in output.splitlines():
        line = raw.strip()
        m = _DEPENDS.match(line)
        if m:
            name = m.group(1)
            ax = {x.strip() for x in m.group(2).split(",") if x.strip()}
            result.setdefault(name, set()).update(ax)
            continue
        m = _NO_AXIOM.match(line)
        if m:
            result.setdefault(m.group(1), set())
    return result


def declared_axioms(text: str) -> List[str]:
    """源码里用 `axiom` 关键字声明的公理名（自定义公理必须登记）。"""
    from .lean_scan import strip_comments

    return _AXIOM_DECL.findall(strip_comments(text))


def audited_names(audit_text: str) -> Set[str]:
    from .lean_scan import strip_comments

    return set(_PRINT_AXIOMS.findall(strip_comments(audit_text)))


@dataclass
class AuditResult:
    ran: bool = False
    ok: bool = False
    output: str = ""
    stderr: str = ""
    axioms: Dict[str, Set[str]] = field(default_factory=dict)
    error: str = ""
    returncode: int = 0

    def tail(self, n: int = 25) -> str:
        text = (self.output + "\n" + self.stderr).strip()
        lines = text.splitlines()
        return "\n".join(lines[-n:])


def run(root: Path, audit_file: str = "Audit.lean", timeout: int = 1800) -> AuditResult:
    path = root / audit_file
    res = AuditResult()
    if not path.is_file():
        res.error = "找不到公理审计文件 {}".format(audit_file)
        return res
    lake = shutil.which("lake", path=str(elan_bin())) if elan_bin() else shutil.which("lake")
    if not lake:
        res.error = "PATH 里没有 lake（先装 elan）"
        return res
    try:
        proc = subprocess.run(
            [lake, "env", "lean", audit_file],
            cwd=str(root), capture_output=True, text=True,
            timeout=timeout, env=lean_env(),
        )
    except subprocess.TimeoutExpired:
        res.error = "公理审计超时（{} 秒）".format(timeout)
        return res
    except OSError as exc:
        res.error = "跑不起来：{}".format(exc)
        return res

    res.ran = True
    res.returncode = proc.returncode
    res.output, res.stderr = proc.stdout, proc.stderr
    res.ok = proc.returncode == 0
    if res.ok:
        res.axioms = parse_axioms(proc.stdout)
    else:
        res.error = "lake env lean {} 返回 {}".format(audit_file, proc.returncode)
    return res


def build(root: Path, timeout: int = 1800) -> Tuple[bool, str]:
    lake = shutil.which("lake", path=str(elan_bin())) if elan_bin() else shutil.which("lake")
    if not lake:
        return False, "PATH 里没有 lake（先装 elan）"
    try:
        proc = subprocess.run([lake, "build"], cwd=str(root), capture_output=True,
                              text=True, timeout=timeout, env=lean_env())
    except subprocess.TimeoutExpired:
        return False, "lake build 超时（{} 秒）".format(timeout)
    except OSError as exc:
        return False, "跑不起来：{}".format(exc)
    text = (proc.stdout or "") + (proc.stderr or "")
    return proc.returncode == 0, text
