import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from mathlean import statements

HEADER = "| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |\n|---|---|---|---|---|---|\n"


class TargetsTest(unittest.TestCase):
    def test_only_proved_and_deduped(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "docs").mkdir()
            (root / "docs" / "CLAIMS.md").write_text(
                HEADER
                + "| C1 | PROVED | 甲 | Foo.a | — | — |\n"
                + "| C2 | PROVED | 乙 | Foo.a | — | — |\n"
                + "| C3 | CONDITIONAL | 丙 | Foo.c | — | 假设：x |\n"
                + "| C4 | PROVED | 丁 | `Foo.d` | — | — |\n",
                encoding="utf-8")
            self.assertEqual(statements.targets(_cfg(root)), ["Foo.a", "Foo.d"])

    def test_no_ledger(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(statements.targets(_cfg(Path(d))), [])


class RenderTest(unittest.TestCase):
    def test_appends_one_example_per_target(self):
        text = statements.render("import Mathlib\n\nnamespace Challenge\nend Challenge", ["Foo.a", "Foo.b"])
        self.assertIn("example : Challenge.Foo.a := Foo.a", text)
        self.assertIn("example : Challenge.Foo.b := Foo.b", text)
        # 挑战文件原文必须完整保留在前面
        self.assertTrue(text.startswith("import Mathlib"))

    def test_no_targets_still_renders(self):
        text = statements.render("import Mathlib", [])
        self.assertNotIn("example :", text)


class RunTest(unittest.TestCase):
    def test_skipped_when_challenge_missing(self):
        with tempfile.TemporaryDirectory() as d:
            res = statements.run(_cfg(Path(d), lib="Foo"))
            self.assertTrue(res.skipped)
            self.assertFalse(res.ran)
            self.assertIn(statements.CHALLENGE_FILE, res.error)

    def test_skipped_when_no_proved_rows(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Statements.lean").write_text("import Mathlib", encoding="utf-8")
            (root / "docs").mkdir()
            (root / "docs" / "CLAIMS.md").write_text(
                HEADER + "| C1 | OPEN | 甲 | — | — | — |\n", encoding="utf-8")
            res = statements.run(_cfg(root, lib="Foo"))
            self.assertTrue(res.skipped)


class RunVerdictTest(unittest.TestCase):
    """编译器返回非零时，门必须判失败，且把 Lean 的原话带出来。"""

    def test_nonzero_exit_is_failure(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Statements.lean").write_text("import Mathlib", encoding="utf-8")
            (root / "docs").mkdir()
            (root / "docs" / "CLAIMS.md").write_text(
                HEADER + "| C1 | PROVED | 甲 | Foo.a | — | — |\n", encoding="utf-8")
            fake = subprocess.CompletedProcess(
                args=[], returncode=1,
                stdout="type mismatch\n  Foo.a : P\nbut is expected to have type Q\n",
                stderr="")
            with mock.patch("mathlean.statements.shutil.which", return_value="/usr/bin/lake"), \
                 mock.patch("mathlean.statements.subprocess.run", return_value=fake):
                res = statements.run(_cfg(root, lib="Foo"))
            self.assertTrue(res.ran)
            self.assertFalse(res.ok)
            self.assertEqual(res.compared, ["Foo.a"])
            self.assertIn("type mismatch", "\n".join(statements.failures(res)))


def _cfg(root: Path, lib: str = "Foo"):
    from mathlean.config import Config
    return Config(root=root, lib=lib)


if __name__ == "__main__":
    unittest.main()
