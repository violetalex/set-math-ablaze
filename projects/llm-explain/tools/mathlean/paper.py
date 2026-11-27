"""论文侧核对：LaTeX 里的定理环境是否都被台账覆盖。

用法：`mathlean ledger --file CLAIMS.md --tex paper.tex`

规则：
  * theorem / proposition / lemma / corollary / openproblem / hypothesis/definition
    带 \\label 的必须被台账引用到，否则算错误；
  * remark 带 \\label 的缺了只算警告——大多数 remark 是解释性的，可以合并进别的行，
    但**合并必须在台账里写明**，所以这里只提醒；
  * 没有 \\label 的环境无法追踪，只计数，不判定。
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple

STRICT_ENVS = ("theorem", "proposition", "lemma", "corollary", "openproblem",
               "hypothesis", "definition")
LOOSE_ENVS = ("remark", "conjecture", "example")
ALL_ENVS = STRICT_ENVS + LOOSE_ENVS

# 可选参数可以带一层嵌套方括号（\cite[Theorem~5.2]{KNSS} 就是这样）。
_OPT = r"(?:\[(?:[^\[\]]|\[[^\[\]\n]*\])*\])?"
_BEGIN = re.compile(
    r"\\begin\{(" + "|".join(ALL_ENVS) + r")\}"
    + _OPT +
    r"\s*\\label\{([^}]*)\}",
    re.S,
)
_ANY_BEGIN = re.compile(r"\\begin\{(" + "|".join(ALL_ENVS) + r")\}")


@dataclass
class TexEnv:
    kind: str
    label: str
    line: int


def environments(text: str) -> List[TexEnv]:
    """抽出所有定理类环境及其紧随的 \\label（没有 label 则记空串）。"""
    out: List[TexEnv] = []
    for m in _ANY_BEGIN.finditer(text):
        lab = _BEGIN.match(text, m.start())
        label = lab.group(2) if lab else ""
        out.append(TexEnv(m.group(1), label, text.count("\n", 0, m.start()) + 1))
    return out


def read_tex(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def _mentions(label: str, text: str) -> bool:
    """label 是否在文本里出现，且不是更长 label 的前缀（thm:main ≠ thm:main2）。"""
    return re.search(re.escape(label) + r"(?![A-Za-z0-9:\-])", text) is not None


def coverage(tex_text: str, ledger_text: str) -> Tuple[List[TexEnv], List[TexEnv], List[TexEnv]]:
    """返回 (缺失, 覆盖到, 无 label)。按 label 是否出现在台账文本里判断。"""
    missing: List[TexEnv] = []
    covered: List[TexEnv] = []
    unlabeled: List[TexEnv] = []
    for env in environments(tex_text):
        if not env.label:
            unlabeled.append(env)
        elif _mentions(env.label, ledger_text):
            covered.append(env)
        else:
            missing.append(env)
    return missing, covered, unlabeled


def summarize(missing: List[TexEnv], covered: List[TexEnv], unlabeled: List[TexEnv]) -> str:
    strict = [e for e in missing if e.kind in STRICT_ENVS]
    return "论文环境 {} 个：覆盖 {}、缺 {}（定理类 {}）、无 label {}".format(
        len(missing) + len(covered) + len(unlabeled), len(covered), len(missing),
        len(strict), len(unlabeled))
