"""kernel 重放（replay）：在编译产物上再验一遍，而不是在构建上。

`build` 门信任的是 elaborator：它会展开宏、跑 tactic、执行 `addDecl` 之类的逃逸口。
真正决定"这个证明成立"的是 kernel，而 `lake build` 通过并不等价于 kernel 接受——
Alpöge 那份证明里就有 `kexactB` / `kcopy` 直接假定证明项、绕过 elaborator 检查的构造，
是靠事后 kernel 重放才兜住的。

`leanchecker` 读的是 `.olean`（编译产物），把它们逐条交给 kernel 重新检查。
这和 `lake build` 是两条不同的路径：build 走 elaborator，replay 只走 kernel。

**能力的边界要说清楚。** `leanchecker` 是 Lean 自带的，与本工程用的是同一个 kernel
实现——它防的是"elaborator 环节被绕过"，防不了"kernel 本身有 bug"。
真正独立的实现（nanoda，Rust 写的）不在 Lean 发行版里，需要单独安装；
本命令预留 `--checker` 参数，将来接上即可。
"""

from __future__ import annotations

import json
import shutil
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from .audit import elan_bin, lean_env
from .config import Config
from .lean_scan import library_sources


@dataclass
class ModuleResult:
    module: str
    ok: bool
    duration: float = 0.0
    output: str = ""


@dataclass
class Result:
    ran: bool = False
    ok: bool = False
    error: str = ""
    modules: List[ModuleResult] = field(default_factory=list)
    lean_version: str = ""
    mathlib_rev: str = ""
    checker: str = "leanchecker"

    def failed(self) -> List[ModuleResult]:
        return [m for m in self.modules if not m.ok]


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def entry_modules(root: Path, lib: str) -> List[str]:
    """要重放的模块。

    优先只重放入口模块（`<库名>.lean`）：`leanchecker` 会顺着 import 图把依赖一起检查，
    逐个模块跑一遍是重复劳动。没有入口文件时退回全部模块。
    """
    files = library_sources(root, lib)
    mods = [module_name(p, root) for p in files]
    if lib in mods:
        return [lib]
    return sorted(mods)


def mathlib_rev(root: Path) -> str:
    path = root / "lake-manifest.json"
    if not path.is_file():
        return ""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, OSError):
        return ""
    for pkg in data.get("packages", []):
        if pkg.get("name") == "mathlib":
            return str(pkg.get("rev") or "")
    return ""


def lean_version(root: Path) -> str:
    bin_dir = elan_bin()
    lean = shutil.which("lean", path=str(bin_dir)) if bin_dir else shutil.which("lean")
    if not lean:
        return ""
    try:
        proc = subprocess.run([lean, "--version"], capture_output=True, text=True,
                              timeout=60, env=lean_env())
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return (proc.stdout or "").strip().splitlines()[0] if proc.stdout else ""


def run(cfg: Config, modules: Optional[Sequence[str]] = None,
        timeout: int = 3600, checker: str = "leanchecker") -> Result:
    res = Result(checker=checker)
    if not cfg.lib:
        res.error = "不知道库名；在配置里设置 [project] lib"
        return res

    names = list(modules) if modules else entry_modules(cfg.root, cfg.lib)
    if not names:
        res.error = "没有找到属于库 {} 的 .lean 文件".format(cfg.lib)
        return res

    lake = shutil.which("lake", path=str(elan_bin())) if elan_bin() else shutil.which("lake")
    if not lake:
        res.error = "PATH 里没有 lake（先装 elan）"
        return res

    res.lean_version = lean_version(cfg.root)
    res.mathlib_rev = mathlib_rev(cfg.root)
    res.ran = True

    for mod in names:
        t0 = time.time()
        try:
            proc = subprocess.run(
                [lake, "env", checker, mod],
                cwd=str(cfg.root), capture_output=True, text=True,
                timeout=timeout, env=lean_env(),
            )
        except subprocess.TimeoutExpired:
            res.modules.append(ModuleResult(mod, False, time.time() - t0,
                                            "超时（{} 秒）".format(timeout)))
            continue
        except OSError as exc:
            res.modules.append(ModuleResult(mod, False, time.time() - t0, str(exc)))
            continue
        out = ((proc.stdout or "") + (proc.stderr or "")).strip()
        res.modules.append(ModuleResult(mod, proc.returncode == 0,
                                        time.time() - t0, out))

    res.ok = all(m.ok for m in res.modules)
    if not res.ok:
        res.error = "{} 个模块被 kernel 拒绝".format(len(res.failed()))
    return res


def summary_lines(res: Result, limit: int = 12) -> List[str]:
    lines: List[str] = []
    if res.lean_version:
        lines.append("Lean      {}".format(res.lean_version))
    if res.mathlib_rev:
        lines.append("Mathlib   {}".format(res.mathlib_rev[:12]))
    lines.append("检查器    {}".format(res.checker))
    for m in res.modules:
        mark = "✔" if m.ok else "✘"
        lines.append("{} {:<32} {:>6.2f}s".format(mark, m.module, m.duration))
        if not m.ok:
            for l in m.output.splitlines()[:limit]:
                lines.append("    " + l)
    return lines
