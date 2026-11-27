"""自检：`mathlean selfcheck`。

一个检查器如果没人验证过它真的会拦，那它就只是个装饰。
这里造一个临时工程，然后**故意弄坏**每一种情形，看门禁是否按预期亮红灯。

默认只跑不依赖 Lean 的门（秒级）；加 `--with-lean` 连编译和公理审计一起验。
"""

from __future__ import annotations

import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, List, Optional, Tuple

from . import checks
from .config import load
from .scaffold import new_project

BASE_CLAIMS = """\
# 命题台账

| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |
|---|---|---|---|---|---|
| C1 | PROVED | 偶数加偶数仍是偶数 | IsEven.add | — | 自检样例 |
"""


@dataclass
class Scenario:
    name: str
    expect_gate: Optional[str]   # 期望失败的门的名字；None 表示应当全部通过
    mutate: Callable[[Path], None]
    expect_pass_gate: Optional[str] = None


def _append(rel: str, text: str) -> Callable[[Path], None]:
    def run(root: Path) -> None:
        p = root / rel
        p.write_text(p.read_text(encoding="utf-8") + text, encoding="utf-8")
    return run


def _write(rel: str, text: str) -> Callable[[Path], None]:
    def run(root: Path) -> None:
        (root / rel).write_text(text, encoding="utf-8")
    return run


def _replace(rel: str, old: str, new: str) -> Callable[[Path], None]:
    def run(root: Path) -> None:
        p = root / rel
        p.write_text(p.read_text(encoding="utf-8").replace(old, new), encoding="utf-8")
    return run


SCENARIOS: List[Scenario] = [
    Scenario("干净工程", None, lambda root: None),
    Scenario("真写了 sorry", "sorry",
             _append("Lib/Basic.lean", "\ntheorem bad : True := by\n  sorry\n")),
    Scenario("用了 native_decide", "sorry",
             _append("Lib/Basic.lean", "\nexample : (1 : Nat) = 1 := by\n  native_decide\n")),
    Scenario("sorry 只出现在注释里", None,
             _append("Lib/Basic.lean", "\n-- 这里不许写 sorry\n")),
    Scenario("PROVED 的声明不存在", "ledger",
             _replace("docs/CLAIMS.md", "IsEven.add", "NoSuchLemma")),
    Scenario("PROVED 没有公理审计", "ledger",
             _replace("Audit.lean", "#print axioms Lib.IsEven.add", "")),
    Scenario("CONDITIONAL 没写假设", "ledger",
             _replace("docs/CLAIMS.md", "| C1 | PROVED |",
                      "| C1 | CONDITIONAL |")),
    Scenario("REFUTED 没给反例", "ledger",
             _replace("docs/CLAIMS.md", "| C1 | PROVED |",
                      "| C1 | REFUTED |")),
    Scenario("非法状态", "ledger",
             _replace("docs/CLAIMS.md", "| C1 | PROVED |", "| C1 | MAYBE |")),
    Scenario("依赖成环", "ledger",
             _write("docs/CLAIMS.md",
                    "| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |\n"
                    "|---|---|---|---|---|---|\n"
                    "| C1 | PROVED | 甲 | IsEven.add | C2 | — |\n"
                    "| C2 | OPEN | 乙 | — | C1 | 卡在 C1 |\n")),
    Scenario("阶段产物还是模板", "docs",
             _replace("mathlean.ini", "strict-docs = false", "strict-docs = true")),
    Scenario("未登记的自定义公理", "axioms",
             _append("Lib/Basic.lean", "\naxiom shortcut : False\n")),
    Scenario("登记过的自定义公理放行", None,
             _append("Lib/Basic.lean", "\naxiom shortcut : False\n")),
]


def _prepare(base: Path, lib: str) -> Path:
    mathlib = base / "pkgs" / "mathlib"
    (mathlib / "Mathlib").mkdir(parents=True, exist_ok=True)
    (mathlib / "Mathlib" / "Init.lean").write_text("-- fake\n", encoding="utf-8")
    dest = base / "proj"
    new_project(dest, lib, mathlib=str(mathlib))
    (dest / "docs" / "CLAIMS.md").write_text(BASE_CLAIMS, encoding="utf-8")
    return dest


def run(keep: bool = False, with_lean: bool = False) -> Tuple[List[dict], bool]:
    tmp = Path(tempfile.mkdtemp(prefix="mathlean-selfcheck-"))
    results: List[dict] = []
    all_ok = True
    try:
        for sc in SCENARIOS:
            root = _prepare(tmp / sc.name.replace(" ", "_"), "Lib")
            if sc.name == "登记过的自定义公理放行":
                ini = root / "mathlean.ini"
                ini.write_text(ini.read_text(encoding="utf-8") + "shortcut = 自检样例\n",
                               encoding="utf-8")
            sc.mutate(root)

            cfg = load(root)
            rep = checks.run(cfg, build=False, run_audit=False)
            failed = {r.name for r in rep.results if not r.ok and not r.skipped}

            if sc.expect_gate is None:
                ok = not failed
                detail = "全部通过" if ok else "意外失败：" + ", ".join(sorted(failed))
            else:
                ok = failed == {sc.expect_gate}
                detail = ("按预期被 {} 拦下".format(sc.expect_gate) if ok
                          else "实际失败的门：{}".format(", ".join(sorted(failed)) or "无"))
            all_ok = all_ok and ok
            results.append({"scenario": sc.name, "ok": ok, "detail": detail})

        if with_lean:
            root = _prepare(tmp / "with_lean", "Lib")
            cfg = load(root)
            rep = checks.run(cfg, build=True, run_audit=True)
            ok = rep.ok
            failed = [r.name for r in rep.results if not r.ok]
            all_ok = all_ok and ok
            results.append({
                "scenario": "完整门禁（含 lake build 与公理审计）",
                "ok": ok,
                "detail": "全部通过" if ok else "失败：" + ", ".join(failed),
            })
    finally:
        if not keep:
            shutil.rmtree(tmp, ignore_errors=True)
        else:
            print("保留临时目录：{}".format(tmp))
    return results, all_ok
