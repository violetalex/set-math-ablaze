import tempfile
import unittest
from pathlib import Path

from mathlean import frontier

HEADER = "| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |\n|---|---|---|---|---|---|\n"


class ClassifyTest(unittest.TestCase):
    def test_axiom_beats_everything(self):
        # 公理即使出现在 Mathlib 的模块里，也必须单独列出来
        self.assertEqual(frontier.classify("axiom", "Mathlib.Algebra.Group.Basic"),
                         frontier.AXIOM)
        self.assertEqual(frontier.classify("axiom", "Init.Core"), frontier.AXIOM)

    def test_core_before_kind(self):
        self.assertEqual(frontier.classify("theorem", "Init.Prelude"), frontier.CORE)
        self.assertEqual(frontier.classify("definition", "Lean.Meta.Basic"), frontier.CORE)
        self.assertEqual(frontier.classify("definition", "Std.Data.HashMap"), frontier.CORE)

    def test_tactic_support(self):
        self.assertEqual(frontier.classify("theorem", "Mathlib.Tactic.Ring.Common"),
                         frontier.TACTIC)
        # 策略模块里的定义同样归策略，不是"数学定理"
        self.assertEqual(frontier.classify("definition", "Mathlib.Tactic.FieldSimp.Lemmas"),
                         frontier.TACTIC)

    def test_theorem_vs_definition(self):
        self.assertEqual(frontier.classify("theorem", "Mathlib.Analysis.SpecialFunctions.Sqrt"),
                         frontier.THEOREM)
        # 实例投影数量巨大但不是命题，不能混进审计面
        self.assertEqual(
            frontier.classify("definition", "Mathlib.Algebra.Group.Defs"),
            frontier.DEFINITION)

    def test_unknown_kind_is_treated_as_axiom(self):
        self.assertEqual(frontier.classify("unknown", "Mathlib.X"), frontier.AXIOM)


class ModuleNameTest(unittest.TestCase):
    def test_path_to_module(self):
        root = Path("/p")
        self.assertEqual(frontier.module_name(root / "Foo" / "Bar.lean", root), "Foo.Bar")
        self.assertEqual(frontier.module_name(root / "Foo.lean", root), "Foo")

    def test_project_modules_sorted_and_deduped(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Foo").mkdir()
            (root / "Foo" / "A.lean").write_text("", encoding="utf-8")
            (root / "Foo" / "B.lean").write_text("", encoding="utf-8")
            (root / "Foo.lean").write_text("", encoding="utf-8")
            self.assertEqual(frontier.project_modules(root, "Foo"),
                             ["Foo", "Foo.A", "Foo.B"])


class LedgerTargetsTest(unittest.TestCase):
    def test_only_proved_rows(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "docs").mkdir()
            (root / "docs" / "CLAIMS.md").write_text(
                HEADER
                + "| C1 | PROVED | 甲 | Foo.a | — | — |\n"
                + "| C2 | PROVED-INFORMAL | 乙 | — | — | — |\n"
                + "| C3 | PROVED | 丙 | Foo.c | — | — |\n",
                encoding="utf-8")
            cfg = _cfg(root)
            self.assertEqual(frontier.ledger_targets(cfg), ["Foo.a", "Foo.c"])


class RenderTest(unittest.TestCase):
    def test_substitution(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Foo").mkdir()
            (root / "Foo" / "A.lean").write_text("", encoding="utf-8")
            skel = root / "tools" / "skeleton"
            skel.mkdir(parents=True)
            (skel / "Frontier.lean").write_text(
                "import __LIB_IMPORT__\n"
                "def t : List Name := [__TARGETS__]\n"
                "def m : List Name := [__PROJECT_MODULES__]\n"
                'def o : String := "__OUTPUT__"\n',
                encoding="utf-8")
            cfg = _cfg(root, lib="Foo")
            out = Path("/tmp/x.json")
            text = frontier.render(cfg, ["Foo.a", "Foo.b"], out)
            self.assertIn("import Foo", text)
            self.assertIn("`Foo.a, `Foo.b", text)
            self.assertIn("`Foo.A", text)
            self.assertIn("/tmp/x.json", text)

    def test_missing_template_is_reported(self):
        with tempfile.TemporaryDirectory() as d:
            cfg = _cfg(Path(d), lib="Foo")
            with self.assertRaises(FileNotFoundError):
                frontier.render(cfg, ["Foo.a"], Path("/tmp/x.json"))


class MarkdownTest(unittest.TestCase):
    def test_sections_and_counts(self):
        res = frontier.Result(ran=True, ok=True)
        res.targets["Foo.a"] = frontier.Target(
            name="Foo.a",
            project=["Foo.a", "Foo.b"],
            external=[
                frontier.Item("propext", "axiom", "Init.Core"),
                frontier.Item("Real.sqrt_pos", "theorem", "Mathlib.Analysis.Sqrt"),
                frontier.Item("ring_lemma", "theorem", "Mathlib.Tactic.Ring.Common"),
                frontier.Item("AddMonoid.toZero", "definition", "Mathlib.Algebra.Group.Defs"),
                frontier.Item("id", "definition", "Init.Core"),
            ])
        md = frontier.to_markdown(res, _cfg(Path("/tmp"), lib="Foo"))
        self.assertIn("## 公理", md)
        self.assertIn("## 数学定理", md)
        self.assertIn("`Real.sqrt_pos`", md)
        self.assertIn("## 策略支撑", md)
        self.assertIn("## 定义与实例", md)
        # 公理必须出现在公理节，不能混进数学定理节
        thm_section = md.split("## 数学定理")[1].split("## 策略支撑")[0]
        self.assertNotIn("propext", thm_section)
        # 定义不算定理
        self.assertNotIn("AddMonoid.toZero", thm_section)


def _cfg(root: Path, lib: str = "Foo"):
    from mathlean.config import Config
    return Config(root=root, lib=lib)


if __name__ == "__main__":
    unittest.main()
