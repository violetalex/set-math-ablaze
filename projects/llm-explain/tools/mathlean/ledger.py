"""`docs/CLAIMS.md` 台账：解析与一致性检查。

台账是唯一真相：论文里每一句「我们证明了」都要能追到一行。
检查分两类：
  * 行内规则（状态、必填项）；
  * 交叉规则（Lean 声明存在、已审计、公理在白名单里、依赖不成环）。
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

STATUSES = (
    "PROVED",
    "PROVED-INFORMAL",
    "CONDITIONAL",
    "OPEN",
    "REFUTED",
    "INFORMAL-ONLY",
    "CITED",
)
PROVED = "PROVED"

ID_RE = re.compile(r"[A-Z]{1,4}[0-9]+")

# 「理解」列的可选值：机器证明不等于有人读懂，这一列把这个差别写进台账。
UNDERSTOOD = ("yes", "partial", "no")
_FENCE = re.compile(r"^\s*(```|~~~)")
_DEP_SPLIT = re.compile(r"[,，、;；\s]+")


@dataclass
class Row:
    id: str
    status: str
    statement: str
    lean: str
    deps_raw: str
    note: str
    line: int
    understood: str = ""

    @property
    def deps(self) -> List[str]:
        out = []
        for tok in _DEP_SPLIT.split(self.deps_raw.strip()):
            tok = tok.strip("`* ")
            if tok and tok not in ("—", "-", "–", "无"):
                out.append(tok)
        return out


@dataclass
class Problem:
    level: str  # error | warning
    where: str
    message: str

    def __str__(self) -> str:
        return "{} {}: {}".format(self.level.upper(), self.where, self.message)


@dataclass
class Report:
    rows: List[Row] = field(default_factory=list)
    problems: List[Problem] = field(default_factory=list)

    def error(self, where: str, message: str) -> None:
        self.problems.append(Problem("error", where, message))

    def warn(self, where: str, message: str) -> None:
        self.problems.append(Problem("warning", where, message))

    @property
    def errors(self) -> List[Problem]:
        return [p for p in self.problems if p.level == "error"]

    @property
    def warnings(self) -> List[Problem]:
        return [p for p in self.problems if p.level == "warning"]

    def counts(self) -> Dict[str, int]:
        out = {s: 0 for s in STATUSES}
        for r in self.rows:
            out[r.status] = out.get(r.status, 0) + 1
        return out


def split_row(line: str) -> List[str]:
    """按未转义的 `|` 切分表格行。"""
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|") and not s.endswith("\\|"):
        s = s[:-1]
    cells, buf, esc = [], [], False
    for ch in s:
        if esc:
            buf.append(ch)
            esc = False
        elif ch == "\\":
            esc = True
        elif ch == "|":
            cells.append("".join(buf).strip())
            buf = []
        else:
            buf.append(ch)
    cells.append("".join(buf).strip())
    return cells


def clean(cell: str) -> str:
    return cell.strip().strip("`").strip()


def is_placeholder(cell: str) -> bool:
    return clean(cell) in ("—", "-", "–", "无", "")


def has_understood_column(text: str) -> bool:
    """表头里有没有「理解」列。有，这一列就按严格规则检查。"""
    for line in text.splitlines():
        if not line.lstrip().startswith("|"):
            continue
        cells = split_row(line)
        if cells and clean(cells[0]).upper() == "ID":
            return any("理解" in c for c in cells)
    return False


def parse(text: str) -> List[Row]:
    rows: List[Row] = []
    with_understood = has_understood_column(text)
    fence = False
    for lineno, line in enumerate(text.splitlines(), start=1):
        if _FENCE.match(line):
            fence = not fence
            continue
        if fence or not line.lstrip().startswith("|"):
            continue
        cells = split_row(line)
        if len(cells) < (7 if with_understood else 6):
            continue
        cid = clean(cells[0])
        if not ID_RE.fullmatch(cid):
            continue
        if with_understood:
            understood, note = clean(cells[5]), cells[6]
        else:
            understood, note = "", cells[5]
        rows.append(Row(
            id=cid,
            status=clean(cells[1]).upper(),
            statement=clean(cells[2]),
            lean=clean(cells[3]),
            deps_raw=cells[4],
            note=note,
            line=lineno,
            understood=understood,
        ))
    return rows


def names_match(a: str, b: str) -> bool:
    a, b = clean(a), clean(b)
    return a == b or a.endswith("." + b) or b.endswith("." + a)


def _find_cycle(rows: Sequence[Row]) -> Optional[List[str]]:
    """依赖 DAG 里找环；返回环上的 ID 序列，没有环返回 None。"""
    graph = {r.id: [d for d in r.deps if ID_RE.fullmatch(d)] for r in rows}
    state: Dict[str, int] = {}  # 0=未访问 1=栈上 2=完成
    stack: List[str] = []

    def visit(node: str) -> Optional[List[str]]:
        state[node] = 1
        stack.append(node)
        for nxt in graph.get(node, []):
            if nxt not in graph:
                continue
            st = state.get(nxt, 0)
            if st == 1:
                i = stack.index(nxt)
                return stack[i:] + [nxt]
            if st == 0:
                found = visit(nxt)
                if found:
                    return found
        stack.pop()
        state[node] = 2
        return None

    for node in graph:
        if state.get(node, 0) == 0:
            found = visit(node)
            if found:
                return found
    return None


def validate(
    rows: Sequence[Row],
    decls: Iterable[str] = (),
    audited_names: Optional[Iterable[str]] = (),
    axiom_map: Optional[Dict[str, Set[str]]] = None,
    allowed_axioms: Sequence[str] = (),
    require_understood: bool = False,
) -> Report:
    """行内 + 交叉检查。

    decls          源码里存在的声明全名；
    audited_names  Audit.lean 里出现 `#print axioms` 的名字（静态读取，不需要跑 Lean）；
                   None 表示没有审计文件，跳过这一项；空集合表示有文件但一条都没有 —— 一样报错。
    axiom_map      跑 Lean 得到的 {声明: 公理集合}；None 表示没跑，跳过公理成员检查。
    """
    report = Report(rows=list(rows))
    decl_set = set(decls)
    audit_set = None if audited_names is None else set(audited_names)
    allowed = set(allowed_axioms)

    seen: Set[str] = set()
    for r in rows:
        where = "{} (第 {} 行)".format(r.id, r.line)
        if r.id in seen:
            report.error(where, "ID 重复")
        seen.add(r.id)

        if require_understood:
            val = r.understood.strip().lower()
            if is_placeholder(val):
                if r.status == PROVED:
                    report.error(where, "PROVED 行必须写理解状态（yes / partial / no）")
            elif val not in UNDERSTOOD:
                report.error(where, "非法理解状态 {!r}；允许 {}".format(
                    r.understood, " / ".join(UNDERSTOOD)))
            elif val in ("no", "partial") and is_placeholder(r.note):
                report.error(where, "理解为 {!r} 时，备注必须写明解读写在哪里".format(val))

        if r.status not in STATUSES:
            report.error(where, "非法状态 {!r}；允许 {}".format(r.status, " / ".join(STATUSES)))
            continue

        if r.status == PROVED:
            if is_placeholder(r.lean):
                report.error(where, "PROVED 必须填 Lean 声明名")
                continue
            if decl_set and not any(names_match(d, r.lean) for d in decl_set):
                report.error(where, "源码里找不到声明 {!r}".format(r.lean))
            if audit_set is not None and not any(names_match(a, r.lean) for a in audit_set):
                report.error(where, "Audit.lean 里没有 #print axioms {}".format(r.lean))
            if axiom_map is not None:
                axioms = set()
                for name, ax in axiom_map.items():
                    if names_match(name, r.lean):
                        axioms |= set(ax)
                if "sorryAx" in axioms:
                    report.error(where, "声明依赖 sorryAx（有没补完的证明）")
                extra = axioms - allowed
                if extra:
                    report.error(where, "依赖未登记的公理 {}".format(", ".join(sorted(extra))))
        elif r.status == "CONDITIONAL":
            if "假设" not in r.note:
                report.error(where, "CONDITIONAL 的备注里必须写「假设：……」")
        elif r.status == "REFUTED":
            if "反例" not in r.note:
                report.error(where, "REFUTED 的备注里必须写「反例：……」")
        elif r.status == "CITED":
            if "引用" not in r.note:
                report.error(where, "CITED 的备注里必须写「引用：……」并给出可检索标识符")
        else:  # PROVED-INFORMAL / OPEN / INFORMAL-ONLY
            if is_placeholder(r.note):
                report.error(where, "{} 必须在备注里说明情况".format(r.status))

    # 依赖引用
    ids = {r.id for r in rows}
    for r in rows:
        for d in r.deps:
            if ID_RE.fullmatch(d) and d not in ids:
                report.error("{} (第 {} 行)".format(r.id, r.line),
                             "依赖 {!r} 不在台账里".format(d))
            elif not ID_RE.fullmatch(d):
                report.warn("{} (第 {} 行)".format(r.id, r.line),
                            "依赖列 {!r} 不是台账 ID，已忽略".format(d))

    cycle = _find_cycle(rows)
    if cycle:
        report.error("依赖图", "存在环：{}（循环论证是头号嫌疑）".format(" → ".join(cycle)))

    # 审计过但没进台账的声明
    claimed = {r.lean for r in rows if r.status == PROVED}
    for name in sorted(audit_set or ()):
        if not any(names_match(name, c) for c in claimed):
            report.warn("Audit.lean", "{} 做了公理审计但台账里没有对应行".format(name))

    return report


def summarize(report: Report) -> str:
    counts = report.counts()
    parts = ["{} {}".format(s, counts[s]) for s in STATUSES if counts.get(s)]
    text = "{} 条台账（{}），{} 个错误，{} 个警告".format(
        len(report.rows), "、".join(parts) or "空", len(report.errors), len(report.warnings))
    vals = [r.understood.strip().lower() for r in report.rows
            if r.understood and not is_placeholder(r.understood)]
    if vals:
        seen = ["{} {}".format(v, vals.count(v)) for v in UNDERSTOOD if vals.count(v)]
        text += "；理解 {}".format(" / ".join(seen))
    return text
