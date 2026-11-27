"""调度（search）：在引理 DAG 上决定"下一个该攻哪里"。

现在的编排是"挑一条就绪的引理去做"，没有策略。这个模块把那个选择变成一个
**可复现、可离线评估**的问题：

  * 状态   台账每一行的 status，依赖是否全部已定；
  * 动作   本轮要做的工作项（就绪集合里的前 N 条）；
  * 奖励   下一轮读回日志时，判断这一条的状态有没有前进；
  * 策略   `rr`（按 ID 轮转，基线）/ `greedy`（按分数）/ `ucb`（用历史奖励）。

**为什么先做确定性的一半。** 优化器可以是 agent，但"该做什么"的算术不该由 agent 说了算：
它必须是可测试、可复现的。等真跑起来攒下日志，再谈换 UCB 的常数——先有记录，再谈优化。

**边界。** 动作空间里没有"修改陈述"。陈述由 `Statements.lean` 钉死，由不参与证明的人写；
`statement` 门是这条约束的执行者。调度器只决定顺序，不决定证什么。
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from . import ledger as ledger_mod
from .config import Config

# 终态：不需要再做任何事
TERMINAL = {"PROVED", "REFUTED", "CITED"}

# 依赖已"定"的状态：PROVED 直接可用，CITED 是外部引用，按已知处理
SATISFIED = {"PROVED", "CITED"}

# 进展折算成 0/1/2/3，用来从两轮日志之间推断奖励
RANK = {
    "OPEN": 0,
    "INFORMAL-ONLY": 0,
    "CONDITIONAL": 1,
    "PROVED-INFORMAL": 2,
    "PROVED": 3,
    "CITED": 3,
    "REFUTED": 3,
}

POLICIES = ("rr", "greedy", "ucb")


@dataclass
class Item:
    id: str
    status: str
    statement: str
    fan_in: int = 0
    n_deps: int = 0
    score: float = 0.0
    attempts: int = 0
    reward: float = 0.0

    def to_dict(self) -> Dict[str, object]:
        return {
            "id": self.id,
            "status": self.status,
            "fan_in": self.fan_in,
            "n_deps": self.n_deps,
            "statement_chars": len(self.statement),
            "score": round(self.score, 4),
            "attempts": self.attempts,
        }


@dataclass
class Plan:
    policy: str = "greedy"
    ready: List[Item] = field(default_factory=list)
    blocked: List[Item] = field(default_factory=list)
    terminal: List[str] = field(default_factory=list)
    dead: List[Item] = field(default_factory=list)
    picks: List[Item] = field(default_factory=list)
    note: str = ""


# ── 结构分析 ────────────────────────────────────────────────────────────

def fan_in(rows: Sequence[ledger_mod.Row]) -> Dict[str, int]:
    """每条被其他行依赖的次数。被依赖越多，价值越高。"""
    counts: Dict[str, int] = {r.id: 0 for r in rows}
    for r in rows:
        for d in r.deps:
            if d in counts and d != r.id:
                counts[d] += 1
    return counts


def _status_of(row: ledger_mod.Row) -> str:
    return row.status.strip().upper()


def analyze(rows: Sequence[ledger_mod.Row]) -> Tuple[List[Item], List[Item], List[str], List[Item]]:
    """把台账分成四堆：就绪 / 未就绪 / 终态 / 已死（依赖被反例推翻）。"""
    status = {r.id: _status_of(r) for r in rows}
    counts = fan_in(rows)

    ready: List[Item] = []
    blocked: List[Item] = []
    terminal: List[str] = []
    dead: List[Item] = []

    for r in rows:
        st = status[r.id]
        item = Item(id=r.id, status=st, statement=r.statement,
                    fan_in=counts.get(r.id, 0),
                    n_deps=len([d for d in r.deps if d in status]))
        if st in TERMINAL:
            terminal.append(r.id)
            continue
        deps = [d for d in r.deps if d in status]
        if any(status[d] == "REFUTED" for d in deps):
            dead.append(item)
            continue
        if all(status[d] in SATISFIED for d in deps):
            ready.append(item)
        else:
            blocked.append(item)
    return ready, blocked, terminal, dead


# ── 历史与奖励 ──────────────────────────────────────────────────────────

def runs_dir(root: Path) -> Path:
    return root / "docs" / "RUNS"


def history(root: Path) -> List[Dict[str, object]]:
    d = runs_dir(root)
    if not d.is_dir():
        return []
    out = []
    for p in sorted(d.glob("search-*.json")):
        try:
            out.append(json.loads(p.read_text(encoding="utf-8")))
        except (ValueError, OSError):
            continue
    return out


def attempts_from(logs: Sequence[Dict[str, object]]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for log in logs:
        for pid in log.get("picks", []) or []:
            counts[str(pid)] = counts.get(str(pid), 0) + 1
    return counts


def rewards_from(last: Optional[Dict[str, object]],
                 rows: Sequence[ledger_mod.Row]) -> Dict[str, float]:
    """上一轮挑中的条目，这一轮状态有没有前进。"""
    if not last:
        return {}
    now = {r.id: RANK.get(_status_of(r), 0) for r in rows}
    before = last.get("statuses", {}) or {}
    out: Dict[str, float] = {}
    for pid in last.get("picks", []) or []:
        pid = str(pid)
        if pid not in now:
            continue
        prev = RANK.get(str(before.get(pid, "")), 0)
        out[pid] = 1.0 if now[pid] > prev else 0.0
    return out


# ── 打分 ────────────────────────────────────────────────────────────────

@dataclass
class Weights:
    fan_in: float = 1.0
    length: float = 0.5      # 陈述越长越贵，按 120 字归一
    attempts: float = 0.3    # 试过多次还没成的，降权
    ucb_c: float = 1.0


def score(item: Item, w: Weights, reward_sum: float = 0.0,
          total: int = 0, explore: bool = False) -> float:
    """基础分 = 价值 − 成本。只有 `ucb` 策略才加探索项。

    `greedy` 必须只看分数，否则它和 `ucb` 的对比就没有意义了。
    """
    base = (w.fan_in * item.fan_in
            - w.length * (len(item.statement) / 120.0)
            - w.attempts * item.attempts)
    if explore and item.attempts and total:
        mean = reward_sum / item.attempts
        base += mean + w.ucb_c * math.sqrt(math.log(max(total, 1)) / item.attempts)
    return base


def rank(ready: List[Item], policy: str, w: Weights,
         attempts: Dict[str, int], rewards: Dict[str, float]) -> List[Item]:
    total = sum(attempts.values())
    for it in ready:
        it.attempts = attempts.get(it.id, 0)
        it.reward = rewards.get(it.id, 0.0)
        it.score = score(it, w, it.reward * it.attempts, total,
                         explore=(policy == "ucb"))
    if policy == "rr":
        return sorted(ready, key=lambda i: i.id)
    return sorted(ready, key=lambda i: (-i.score, i.id))


def plan(cfg: Config, policy: str = "greedy", limit: int = 5,
         weights: Optional[Weights] = None) -> Plan:
    w = weights or Weights()
    path = cfg.claims_path
    if not path.is_file():
        return Plan(policy=policy, note="没有 docs/CLAIMS.md")
    rows = ledger_mod.parse(path.read_text(encoding="utf-8", errors="replace"))
    if not rows:
        return Plan(policy=policy, note="台账为空")

    logs = history(cfg.root)
    attempts = attempts_from(logs)
    rewards = rewards_from(logs[-1] if logs else None, rows)

    ready, blocked, terminal, dead = analyze(rows)
    ordered = rank(ready, policy, w, attempts, rewards)
    return Plan(policy=policy, ready=ordered, blocked=blocked, terminal=terminal,
                dead=dead, picks=ordered[:max(limit, 0)])


def write_record(cfg: Config, p: Plan) -> Path:
    rows = ledger_mod.parse(cfg.claims_path.read_text(encoding="utf-8", errors="replace"))
    d = runs_dir(cfg.root)
    d.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    path = d / "search-{}.json".format(stamp)
    payload = {
        "time_utc": stamp,
        "policy": p.policy,
        "picks": [i.id for i in p.picks],
        "ready": len(p.ready),
        "blocked": len(p.blocked),
        "terminal": len(p.terminal),
        "dead": [i.id for i in p.dead],
        "statuses": {r.id: _status_of(r) for r in rows},
        "scored": [i.to_dict() for i in p.ready],
    }
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8")
    return path


def summary_lines(p: Plan) -> List[str]:
    lines = [
        "策略 {}   就绪 {}   未就绪 {}   终态 {}   已死 {}".format(
            p.policy, len(p.ready), len(p.blocked), len(p.terminal), len(p.dead)),
    ]
    if p.note:
        lines.append("（{}）".format(p.note))
    for i, it in enumerate(p.picks, 1):
        lines.append("  {:>2}. {:<6} 分数 {:>6.2f}  被引用 {}  陈述 {} 字  试过 {} 次  [{}]".format(
            i, it.id, it.score, it.fan_in, len(it.statement), it.attempts, it.status))
    if not p.picks and p.ready:
        lines.append("  （limit 为 0）")
    return lines
