"""陈述门（statement）：证的是不是那句话。

`build` 说代码能编译，`axioms` 说公理干净，`ledger` 说声明的名字对得上——
但没有一道门检查**定理的类型就是论文里那句话**。

做法：在工程根放一个 `Statements.lean`，由**不参与证明的人**把每个 `PROVED`
命题按原样重写一遍，放在 `namespace Challenge` 下，名字约定为
`Challenge.<Lean 声明名>`：

    import Mathlib
    import Liouville

    namespace Challenge

    def Liouville.PhiExt_bound : Prop :=
      ∀ (Γ : ℝ → ℝ → ℝ → ℝ) ... , ... → |Liouville.PhiExt Γ Φ₀ ρ ζ t| ≤ ...

    end Challenge

门禁把这份文件原文复制到临时文件，再追加一行

    example : Challenge.Liouville.PhiExt_bound := Liouville.PhiExt_bound

由 elaborator 判定两边类型是否**定义等价**。三条性质让它值得单独成门：

  * 不读证明。证明可以任意改写、任意长，类型不比就不过。
  * 不靠人眼。`P7` 的陈述保真审计是人读，这里可机检。
  * 失败信息是 Lean 自己的 `type mismatch`，带两边类型，直接可读。

它不解决的问题：如果工程自己的**定义**被改过（`R` 不是论文的 `R`），
两边会一起变，比对仍然通过。那一层要靠 `frontier` 里"定义与实例"一节人工核对。
"""

from __future__ import annotations

import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Sequence

from . import ledger as ledger_mod
from .audit import elan_bin, lean_env
from .config import Config

CHALLENGE_FILE = "Statements.lean"
NAMESPACE = "Challenge"

TEMPLATE_HINT = """\
在工程根新建 {}，把每个 PROVED 命题按原样重写一遍：

    import Mathlib
    import {lib}

    namespace {ns}

    def {lib}.example_name : Prop :=
      <原命题>

    end {ns}
""".format(CHALLENGE_FILE, lib="<库名>", ns=NAMESPACE)


@dataclass
class Result:
    ran: bool = False
    ok: bool = False
    skipped: bool = False
    error: str = ""
    compared: List[str] = field(default_factory=list)
    output: str = ""


def challenge_path(cfg: Config) -> Path:
    return cfg.root / CHALLENGE_FILE


def targets(cfg: Config) -> List[str]:
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


def render(challenge: str, names: Sequence[str]) -> str:
    lines = [challenge.rstrip(), "", "-- 以下由 mathlean 生成：类型比对", ""]
    for n in names:
        lines.append("example : {}.{} := {}".format(NAMESPACE, n, n))
    return "\n".join(lines) + "\n"


def run(cfg: Config, timeout: int = 1800) -> Result:
    res = Result()
    path = challenge_path(cfg)
    if not path.is_file():
        res.skipped = True
        res.error = "没有 {}，跳过陈述比对".format(CHALLENGE_FILE)
        return res

    names = targets(cfg)
    if not names:
        res.skipped = True
        res.error = "台账里没有 PROVED 行，无需比对"
        return res

    lake = shutil.which("lake", path=str(elan_bin())) if elan_bin() else shutil.which("lake")
    if not lake:
        res.error = "PATH 里没有 lake（先装 elan）"
        return res

    challenge = path.read_text(encoding="utf-8", errors="replace")
    workdir = Path(tempfile.mkdtemp(prefix="mathlean-stmt-"))
    target = workdir / "StatementCheck.lean"
    target.write_text(render(challenge, names), encoding="utf-8")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", str(target)],
            cwd=str(cfg.root), capture_output=True, text=True,
            timeout=timeout, env=lean_env(),
        )
    except subprocess.TimeoutExpired:
        res.error = "陈述比对超时（{} 秒）".format(timeout)
        return res
    except OSError as exc:
        res.error = "跑不起来：{}".format(exc)
        return res

    res.ran = True
    res.output = (proc.stdout or "") + (proc.stderr or "")
    res.compared = list(names)
    res.ok = proc.returncode == 0
    if not res.ok:
        res.error = "陈述与声明的类型不等价"
    return res


def failures(res: Result, limit: int = 20) -> List[str]:
    return [l for l in res.output.splitlines() if l.strip()][:limit]
