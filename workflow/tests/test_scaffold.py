import shutil
import tempfile
import unittest
from pathlib import Path

from mathlean import docs_gate
from mathlean.scaffold import new_project


class ForceTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="mathlean-scaffold-"))
        self.mathlib = self.tmp / "mathlib"
        (self.mathlib / "Mathlib").mkdir(parents=True)
        (self.mathlib / "Mathlib" / "Init.lean").write_text("-- fake\n", encoding="utf-8")
        self.root = self.tmp / "proj"
        new_project(self.root, "Lib", str(self.mathlib))

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_templates_are_marked(self):
        self.assertTrue(docs_gate.is_stub(self.root / "docs" / "SPEC.md"))

    def test_force_keeps_filled_docs(self):
        spec = self.root / "docs" / "SPEC.md"
        spec.write_text("# 真正写过的规格\n", encoding="utf-8")
        new_project(self.root, "Lib", str(self.mathlib), force=True)
        self.assertIn("真正写过的规格", spec.read_text(encoding="utf-8"))

    def test_force_refreshes_stubs(self):
        spec = self.root / "docs" / "SPEC.md"
        spec.write_text("<!-- mathlean:template -->\n旧的占位\n", encoding="utf-8")
        new_project(self.root, "Lib", str(self.mathlib), force=True)
        self.assertNotIn("旧的占位", spec.read_text(encoding="utf-8"))
        self.assertTrue(docs_gate.is_stub(spec))


if __name__ == "__main__":
    unittest.main()
