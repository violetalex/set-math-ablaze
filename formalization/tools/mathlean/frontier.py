"""审计面（frontier）：这个证明从工程外面借用了什么。

`axioms` 门回答"依赖了哪些公理"，`ledger` 门回答"声明的名字对不对"。
两者都不回答：**证明本体之外，还有哪些事实在被使用，而它们的正确性不由本工程保证。**

frontier 把这个问题变成一个可数的集合：

  * 从台账里每个 `PROVED` 声明出发（也可用 `--target` 指定），
  * 沿**本项目内部**的声明做传递闭包（不进入 Mathlib），
  * 收集闭包里每个声明直接引用的常量，
  * 去掉属于本项目的，剩下的就是审计面，并按来源分类。

在 Mathlib 边界上停下是刻意的：被借来的那条引理就是"一个信任单元"，
核对它的陈述比展开它的证明更有价值。证明规模越大，这个区别越重要——
中段交给 kernel，两端留给人。

分类（`bucket`）：

  * `axiom`  —— 公理或 `sorryAx` 之类，永远排在最前；
  * `core`   —— `Init` / `Lean` / `Std` / `Batteries` / `Lake`，程序语言的基础设施；
  * `tactic` —— `Mathlib.Tactic.*`，`ring` / `field_simp` / `norm_num` 展开出的支撑引理；
  * `math`   —— 其余，这才是真正"借来的数学"。
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from . import ledger as ledger_mod
from .audit import elan_bin, lean_env
from .config import Config
from .lean_scan import library_sources

CORE_PREFIXES = ("Init", "Lean", "Std", "Batteries", "Lake")
TACTIC_PREFIX = "Mathlib.Tactic"

AXIOM = "axiom"
CORE = "core"
TACTIC = "tactic"
THEOREM = "theorem"
DEFINITION = "definition"

BUCKETS = (AXIOM, THEOREM, TACTIC, DEFINITION, CORE)

BUCKET_LABELS = {
    AXIOM: "公理",
    THEOREM: "数学定理",
    TACTIC: "策略支撑",
    DEFINITION: "定义与实例",
    CORE: "语言基础",
}


def classify(kind: str, module: str) -> str:
    """先看是不是公理，再看来源，最后按 kind 区分定理与定义。

    实例投影（`AddCommGroup.toDivisionAddCommMonoid` 之类）数量巨大但不是命题，
    把它们和真正要核对的定理混在一起，审计面就失去意义了。
    """
    if kind in ("axiom", "unknown"):
        return AXIOM
    if module.startswith(CORE_PREFIXES):
        return CORE
    if module.startswith(TACTIC_PREFIX):
        return TACTIC
    if kind == "theorem":
        return THEOREM
    return DEFINITION


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def project_modules(root: Path, lib: str) -> List[str]:
    return sorted({module_name(p, root) for p in library_sources(root, lib)})


def ledger_targets(cfg: Config) -> List[str]:
    """台账里 `PROVED` 行的 Lean 声明名。"""
    path = cfg.claims_path
    if not path.is_file():
        return []
    rows = ledger_mod.parse(path.read_text(encoding="utf-8", errors="replace"))
    out: List[str] = []
    for r in rows:
        if r.status == ledger_mod.PROVED and not ledger_mod.is_placeholder(r.lean):
            name = r.lean.strip().strip("`")
            if name and name not in out:
                out.append(name)
    return out


@dataclass
class Item:
    name: str
    kind: str
    module: str

    @property
    def bucket(self) -> str:
        return classify(self.kind, self.module)


@dataclass
class Target:
    name: str
    project: List[str] = field(default_factory=list)
    external: List[Item] = field(default_factory=list)

    def bucket(self, name: str) -> List[Item]:
        return [i for i in self.external if i.bucket == name]

    def counts(self) -> Dict[str, int]:
        out = {k: 0 for k in BUCKETS}
        for i in self.external:
            out[i.bucket] += 1
        return out


@dataclass
class Result:
    ran: bool = False
    ok: bool = False
    error: str = ""
    targets: Dict[str, Optional[Target]] = field(default_factory=dict)
    missing: List[str] = field(default_factory=list)
    project_modules: List[str] = field(default_factory=list)
    output: str = ""
    stderr: str = ""

    def union(self) -> List[Item]:
        seen: Dict[Tuple[str, str], Item] = {}
        for t in self.targets.values():
            if not t:
                continue
            for i in t.external:
                seen.setdefault((i.name, i.kind), i)
        return sorted(seen.values(), key=lambda i: (i.bucket, i.name))


def _template(cfg: Config) -> Optional[Path]:
    for rel in ("tools/skeleton/Frontier.lean", "tools/lean/Frontier.lean"):
        p = cfg.root / rel
        if p.is_file():
            return p
    return None


def render(cfg: Config, targets: Sequence[str], output: Path) -> str:
    tpl = _template(cfg)
    if tpl is None:
        raise FileNotFoundError(
            "找不到 Frontier.lean 模板；先跑 `mathlean upgrade` 把 tools/ 更新到当前版本")
    text = tpl.read_text(encoding="utf-8")
    mods = project_modules(cfg.root, cfg.lib)
    text = text.replace("__LIB_IMPORT__", cfg.lib)
    text = text.replace("__TARGETS__", ", ".join("`" + t for t in targets))
    text = text.replace("__PROJECT_MODULES__", ", ".join("`" + m for m in mods))
    text = text.replace("__OUTPUT__", str(output).replace("\\", "/"))
    return text


def run(cfg: Config, targets: Optional[Sequence[str]] = None,
        timeout: int = 1800) -> Result:
    res = Result()
    if not cfg.lib:
        res.error = "不知道库名；在配置里设置 [project] lib"
        return res

    names = list(targets) if targets else ledger_targets(cfg)
    if not names:
        res.error = "台账里没有 PROVED 行，也没有用 --target 指定"
        return res
    res.project_modules = project_modules(cfg.root, cfg.lib)

    lake = shutil.which("lake", path=str(elan_bin())) if elan_bin() else shutil.which("lake")
    if not lake:
        res.error = "PATH 里没有 lake（先装 elan）"
        return res

    workdir = Path(tempfile.mkdtemp(prefix="mathlean-frontier-"))
    out_json = workdir / "frontier.json"
    try:
        (workdir / "Frontier.lean").write_text(
            render(cfg, names, out_json), encoding="utf-8")
    except FileNotFoundError as exc:
        res.error = str(exc)
        return res

    try:
        proc = subprocess.run(
            [lake, "env", "lean", str(workdir / "Frontier.lean")],
            cwd=str(cfg.root), capture_output=True, text=True,
            timeout=timeout, env=lean_env(),
        )
    except subprocess.TimeoutExpired:
        res.error = "frontier 超时（{} 秒）".format(timeout)
        return res
    except OSError as exc:
        res.error = "跑不起来：{}".format(exc)
        return res

    res.ran = True
    res.output, res.stderr = proc.stdout, proc.stderr
    if proc.returncode != 0:
        res.error = "lake env lean Frontier.lean 返回 {}".format(proc.returncode)
        return res
    if not out_json.is_file():
        res.error = "Lean 没有写出结果文件（模板里缺 #writeFrontier？）"
        return res

    data = json.loads(out_json.read_text(encoding="utf-8"))
    for name in names:
        entry = data.get("targets", {}).get(name)
        if entry is None:
            res.targets[name] = None
            res.missing.append(name)
            continue
        res.targets[name] = Target(
            name=name,
            project=list(entry.get("project", [])),
            external=[Item(n, k, m) for n, k, m in entry.get("external", [])],
        )
    res.ok = not res.missing
    if res.missing:
        res.error = "源码里找不到这些声明：{}".format(", ".join(res.missing))
    return res


def summary_lines(res: Result) -> List[str]:
    lines: List[str] = []
    live = {k: v for k, v in res.targets.items() if v}
    lines.append("目标 {} 个；项目内声明 {}；外部引用 {}".format(
        len(res.targets),
        len({n for t in live.values() for n in t.project}),
        len(res.union())))
    for name, t in res.targets.items():
        if t is None:
            lines.append("{}  源码里找不到".format(name))
            continue
        c = t.counts()
        lines.append("{}".format(name))
        lines.append("  项目内 {}   外部 {}   公理 {}   数学定理 {}   策略支撑 {}   定义与实例 {}   语言基础 {}".format(
            len(t.project), len(t.external), c[AXIOM], c[THEOREM],
            c[TACTIC], c[DEFINITION], c[CORE]))
        ax = [i.name for i in t.bucket(AXIOM)]
        if ax:
            lines.append("  公理: " + ", ".join(sorted(ax)))
        thms = sorted(i.name for i in t.bucket(THEOREM))
        if thms:
            head = thms[:8]
            more = "" if len(thms) <= 8 else "  …（共 {}）".format(len(thms))
            lines.append("  数学定理: " + ", ".join(head) + more)
    return lines


def to_markdown(res: Result, cfg: Config) -> str:
    live = {k: v for k, v in res.targets.items() if v}
    un = res.union()
    counts: Dict[str, int] = {k: 0 for k in BUCKETS}
    for i in un:
        counts[i.bucket] += 1

    out: List[str] = []
    out.append("# 审计面（frontier）")
    out.append("")
    out.append("> 由 `mathlean frontier` 生成，不要手改。")
    out.append(">")
    out.append("> 口径：从台账 `PROVED` 行出发，沿本项目内部的声明做传递闭包，"
               "收集它们直接引用的外部常量；到 Mathlib 边界为止，不展开。")
    out.append("")
    out.append("## 总览")
    out.append("")
    out.append("| 目标 | 项目内声明 | 外部引用 | 公理 | 数学定理 | 策略支撑 | 定义与实例 | 语言基础 |")
    out.append("|---|---|---|---|---|---|---|---|")
    for name, t in res.targets.items():
        if t is None:
            out.append("| `{}` | — | — | — | — | — | — | 源码里找不到 |".format(name))
            continue
        c = t.counts()
        out.append("| `{}` | {} | {} | {} | {} | {} | {} | {} |".format(
            name, len(t.project), len(t.external), c[AXIOM], c[THEOREM],
            c[TACTIC], c[DEFINITION], c[CORE]))
    out.append("")
    out.append("全部目标合并后：外部引用 {} 条（公理 {}、数学定理 {}、策略支撑 {}、定义与实例 {}、语言基础 {}）。".format(
        len(un), counts[AXIOM], counts[THEOREM], counts[TACTIC],
        counts[DEFINITION], counts[CORE]))
    out.append("")

    axioms = [i for i in un if i.bucket == AXIOM]
    out.append("## 公理")
    out.append("")
    if axioms:
        for i in axioms:
            out.append("- `{}`（{}）".format(i.name, i.module))
    else:
        out.append("（无）")
    out.append("")

    out.append("## 数学定理")
    out.append("")
    thms = [i for i in un if i.bucket == THEOREM]
    if thms:
        out.append("本工程之外、非策略产生的命题。**这一节就是审计面。**")
        out.append("")
        by_mod: Dict[str, List[str]] = {}
        for i in thms:
            by_mod.setdefault(i.module, []).append(i.name)
        for mod in sorted(by_mod):
            names = sorted(by_mod[mod])
            out.append("### `{}`（{}）".format(mod, len(names)))
            out.append("")
            for n in names:
                out.append("- `{}`".format(n))
            out.append("")
    else:
        out.append("（无）")
        out.append("")

    out.append("## 策略支撑")
    out.append("")
    tac = [i for i in un if i.bucket == TACTIC]
    if tac:
        mods: Dict[str, int] = {}
        for i in tac:
            mods[i.module] = mods.get(i.module, 0) + 1
        out.append("`ring` / `field_simp` / `norm_num` 等策略展开产生的引理，共 {} 条，按模块：".format(len(tac)))
        out.append("")
        for mod in sorted(mods, key=lambda m: -mods[m]):
            out.append("- `{}`：{}".format(mod, mods[mod]))
    else:
        out.append("（无）")
    out.append("")

    out.append("## 定义与实例")
    out.append("")
    defs = [i for i in un if i.bucket == DEFINITION]
    if defs:
        mods = {}
        for i in defs:
            mods[i.module] = mods.get(i.module, 0) + 1
        out.append("定义、结构、实例投影等，共 {} 条。它们不是命题，通常不需要逐条核对，"
                   "但**它们决定了定理在说什么**——定义被改过，定理就换了意思。".format(len(defs)))
        out.append("")
        for mod in sorted(mods, key=lambda m: -mods[m])[:15]:
            out.append("- `{}`：{}".format(mod, mods[mod]))
    else:
        out.append("（无）")
    out.append("")

    out.append("## 每个目标的项目内闭包")
    out.append("")
    for name, t in res.targets.items():
        if t is None:
            continue
        out.append("### `{}`".format(name))
        out.append("")
        for n in t.project:
            out.append("- `{}`".format(n))
        out.append("")
    return "\n".join(out)
