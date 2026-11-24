import json
import tempfile
import unittest
from pathlib import Path

from mathlean import ledger, search

HEADER = "| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |\n|---|---|---|---|---|---|\n"


def rows(*specs):
    text = HEADER + "".join(
        "| {} | {} | {} | — | {} | 说明 |\n".format(i, s, "x" * n, d)
        for i, s, d, n in specs)
    return ledger.parse(text)


class AnalyzeTest(unittest.TestCase):
    def test_partition(self):
        r = rows(
            ("C1", "PROVED", "—", 10),
            ("C2", "OPEN", "C1", 10),        # 依赖已定 → 就绪
            ("C3", "OPEN", "C4", 10),        # 依赖未定 → 未就绪
            ("C4", "CONDITIONAL", "—", 10),  # 自己就是未定
            ("C5", "CITED", "—", 10),        # 终态
            ("C6", "OPEN", "C7", 10),        # 依赖被反例推翻 → 已死
            ("C7", "REFUTED", "—", 10),
        )
        ready, blocked, terminal, dead = search.analyze(r)
        # C4 自己没依赖，虽然还是 CONDITIONAL，但它可以被攻
        self.assertEqual({i.id for i in ready}, {"C2", "C4"})
        self.assertEqual({i.id for i in blocked}, {"C3"})
        self.assertEqual(set(terminal), {"C1", "C5", "C7"})
        self.assertEqual({i.id for i in dead}, {"C6"})

    def test_fan_in(self):
        r = rows(
            ("C1", "PROVED", "—", 10),
            ("C2", "OPEN", "C1", 10),
            ("C3", "OPEN", "C1", 10),
        )
        counts = search.fan_in(r)
        self.assertEqual(counts["C1"], 2)
        self.assertEqual(counts["C2"], 0)

    def test_self_dependency_ignored(self):
        r = rows(("C1", "OPEN", "C1", 10))
        self.assertEqual(search.fan_in(r)["C1"], 0)


class RankTest(unittest.TestCase):
    def _items(self):
        return [
            search.Item("C1", "OPEN", "x" * 200, fan_in=0, score=0.0),
            search.Item("C2", "OPEN", "x" * 20, fan_in=3, score=0.0),
        ]

    def test_greedy_prefers_fan_in(self):
        items = self._items()
        ordered = search.rank(items, "greedy", search.Weights(), {}, {})
        self.assertEqual([i.id for i in ordered], ["C2", "C1"])

    def test_round_robin_is_by_id(self):
        items = self._items()
        ordered = search.rank(items, "rr", search.Weights(), {}, {})
        self.assertEqual([i.id for i in ordered], ["C1", "C2"])

    def test_length_penalty(self):
        short = search.Item("C1", "OPEN", "x" * 20, fan_in=1)
        long = search.Item("C2", "OPEN", "x" * 600, fan_in=1)
        w = search.Weights()
        self.assertGreater(search.score(short, w), search.score(long, w))

    def test_attempt_penalty(self):
        it = search.Item("C1", "OPEN", "x" * 20, fan_in=1, attempts=3)
        self.assertLess(search.score(it, search.Weights()),
                        search.score(search.Item("C1", "OPEN", "x" * 20, fan_in=1),
                                     search.Weights()))


class HistoryTest(unittest.TestCase):
    def test_attempts_counted(self):
        logs = [{"picks": ["C1", "C2"]}, {"picks": ["C1"]}]
        self.assertEqual(search.attempts_from(logs), {"C1": 2, "C2": 1})

    def test_reward_is_progress(self):
        r = rows(("C1", "PROVED", "—", 10), ("C2", "OPEN", "—", 10))
        last = {"picks": ["C1", "C2"],
                "statuses": {"C1": "PROVED-INFORMAL", "C2": "OPEN"}}
        rew = search.rewards_from(last, r)
        self.assertEqual(rew["C1"], 1.0)   # PROVED-INFORMAL → PROVED
        self.assertEqual(rew["C2"], 0.0)   # 没动

    def test_no_history(self):
        self.assertEqual(search.rewards_from(None, rows(("C1", "OPEN", "—", 10))), {})


class PlanTest(unittest.TestCase):
    def test_plan_and_record(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "docs" / "RUNS").mkdir(parents=True)
            (root / "docs" / "CLAIMS.md").write_text(
                HEADER
                + "| C1 | PROVED | 甲 | Foo.a | — | 说明 |\n"
                + "| C2 | OPEN | 乙 | — | C1 | 说明 |\n",
                encoding="utf-8")
            cfg = _cfg(root)
            p = search.plan(cfg, policy="greedy", limit=5)
            self.assertEqual([i.id for i in p.picks], ["C2"])
            path = search.write_record(cfg, p)
            data = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(data["picks"], ["C2"])
            self.assertEqual(data["statuses"]["C2"], "OPEN")

    def test_missing_ledger(self):
        with tempfile.TemporaryDirectory() as d:
            p = search.plan(_cfg(Path(d)))
            self.assertEqual(p.picks, [])
            self.assertIn("CLAIMS", p.note)


def _cfg(root: Path, lib: str = "Foo"):
    from mathlean.config import Config
    return Config(root=root, lib=lib)


if __name__ == "__main__":
    unittest.main()
