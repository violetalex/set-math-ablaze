import shutil
import tempfile
import unittest
from pathlib import Path

from mathlean import checks
from mathlean.config import load
from mathlean.scaffold import new_project

CLAIMS = """\
| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |
|---|---|---|---|---|---|
| C1 | PROVED | 偶数加偶数 | IsEven.add | — | 样例 |
"""


class ProjectCase(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="mathlean-test-"))
        mathlib = self.tmp / "pkgs" / "mathlib"
        (mathlib / "Mathlib").mkdir(parents=True)
        (mathlib / "Mathlib" / "Init.lean").write_text("-- fake\n", encoding="utf-8")
        self.root = self.tmp / "proj"
        new_project(self.root, "Lib", mathlib=str(mathlib))
        (self.root / "docs" / "CLAIMS.md").write_text(CLAIMS, encoding="utf-8")
        self.cfg = load(self.root)

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def run_checks(self, **kw):
        return checks.run(self.cfg, build=False, run_audit=False, **kw)


class CleanProjectTest(ProjectCase):
    def test_passes(self):
        rep = self.run_checks()
        failed = [r for r in rep.results if not r.ok and not r.skipped]
        self.assertEqual(failed, [], msg=[str(f) for f in failed])

    def test_lib_inferred(self):
        self.assertEqual(self.cfg.lib, "Lib")

    def test_sorry_skipped_gate_is_not_skip(self):
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertTrue(names["sorry"].ok)
        self.assertFalse(names["sorry"].skipped)


class SorryTest(ProjectCase):
    def test_sorry_fails(self):
        p = self.root / "Lib" / "Basic.lean"
        p.write_text(p.read_text(encoding="utf-8") + "\ntheorem bad : True := by\n  sorry\n",
                     encoding="utf-8")
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertFalse(names["sorry"].ok)

    def test_commented_sorry_passes(self):
        p = self.root / "Lib" / "Basic.lean"
        p.write_text(p.read_text(encoding="utf-8") + "\n-- 不许写 sorry\n", encoding="utf-8")
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertTrue(names["sorry"].ok)


class AxiomTest(ProjectCase):
    def test_unregistered_axiom_fails_even_without_audit(self):
        p = self.root / "Lib" / "Basic.lean"
        p.write_text(p.read_text(encoding="utf-8") + "\naxiom shortcut : False\n",
                     encoding="utf-8")
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertFalse(names["axioms"].ok)


class LedgerGateTest(ProjectCase):
    def test_proved_without_audit_fails(self):
        p = self.root / "Audit.lean"
        p.write_text(p.read_text(encoding="utf-8").replace("#print axioms Lib.IsEven.add", ""),
                     encoding="utf-8")
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertFalse(names["ledger"].ok)


class DocsGateTest(ProjectCase):
    def test_scaffold_templates_count_as_unfilled(self):
        # 新建工程时 SPEC/AUDIT 还是模板；strict 模式下不能算"阶段产物齐全"
        self.cfg.strict_docs = True
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertFalse(names["docs"].ok)
        self.assertIn("模板", names["docs"].summary)

    def test_filled_docs_pass_strict(self):
        self.cfg.strict_docs = True
        for name, body in (("SPEC.md", "# 规格\n\n真内容\n"),
                           ("AUDIT.md", "# 审计\n\n真内容\n")):
            (self.root / "docs" / name).write_text(body, encoding="utf-8")
        rep = self.run_checks()
        names = {r.name: r for r in rep.results}
        self.assertTrue(names["docs"].ok, names["docs"].summary)

    def test_status_lists_stubs(self):
        info = checks.status(self.cfg)
        self.assertIn("SPEC.md", info["stubs"])
        self.assertNotIn("CLAIMS.md", info["stubs"])   # 已被测试覆盖写


class JsonTest(ProjectCase):
    def test_report_is_serialisable(self):
        import json

        rep = self.run_checks()
        text = json.dumps(rep.to_dict(), ensure_ascii=False)
        self.assertIn("results", text)


if __name__ == "__main__":
    unittest.main()
