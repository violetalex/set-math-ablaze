import contextlib
import io
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from mathlean.cli import main

CLAIMS = """\
| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |
|---|---|---|---|---|---|
| C1 | PROVED | 偶数加偶数 | IsEven.add | — | 样例 |
"""


def run_cli(*argv):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = main(list(argv))
    return code, out.getvalue(), err.getvalue()


class CliTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="mathlean-cli-"))
        mathlib = self.tmp / "pkgs" / "mathlib"
        (mathlib / "Mathlib").mkdir(parents=True)
        (mathlib / "Mathlib" / "Init.lean").write_text("-- fake\n", encoding="utf-8")
        self.root = self.tmp / "proj"
        code, _, err = run_cli("new", str(self.root), "Lib", "--mathlib", str(mathlib))
        self.assertEqual(code, 0, err)
        (self.root / "docs" / "CLAIMS.md").write_text(CLAIMS, encoding="utf-8")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_version(self):
        code, out, _ = run_cli("version")
        self.assertEqual(code, 0)
        self.assertIn("mathlean", out)

    def test_check_json(self):
        code, out, _ = run_cli("check", "--root", str(self.root),
                               "--no-build", "--no-audit", "--json")
        data = json.loads(out)
        self.assertEqual(code, 0, out)
        self.assertTrue(data["ok"])
        self.assertIn("results", data)

    def test_check_quiet(self):
        code, out, _ = run_cli("check", "--root", str(self.root),
                               "--no-build", "--no-audit", "--quiet")
        self.assertEqual(code, 0)
        self.assertNotIn("mathlean 1.0.0", out)

    def test_status_json(self):
        code, out, _ = run_cli("status", "--root", str(self.root), "--json")
        data = json.loads(out)
        self.assertEqual(code, 0)
        self.assertEqual(data["ledger"]["rows"], 1)
        self.assertEqual(data["ledger"]["counts"]["PROVED"], 1)

    def test_broken_project_exits_1(self):
        p = self.root / "Lib" / "Basic.lean"
        p.write_text(p.read_text(encoding="utf-8") + "\ntheorem bad : True := by\n  sorry\n",
                     encoding="utf-8")
        code, out, _ = run_cli("check", "--root", str(self.root),
                               "--no-build", "--no-audit", "--json")
        data = json.loads(out)
        self.assertEqual(code, 1)
        self.assertFalse(data["ok"])

    def test_ledger_standalone(self):
        code, out, _ = run_cli("ledger", "--file", str(self.root / "docs" / "CLAIMS.md"), "--json")
        data = json.loads(out)
        self.assertEqual(code, 0, out)
        self.assertEqual(data["rows"], 1)
        self.assertEqual(data["counts"]["PROVED"], 1)
        # 没有 Lean 工程时 PROVED 会给警告，但不报错
        self.assertTrue(any("Lean 工程" in p["message"] for p in data["problems"]))

    def test_ledger_tex_coverage(self):
        tex = self.tmp / "main.tex"
        tex.write_text("\\begin{theorem}\\label{thm:a} x \\end{theorem}\n"
                       "\\begin{theorem}\\label{thm:b} y \\end{theorem}\n", encoding="utf-8")
        code, out, _ = run_cli("ledger", "--file", str(self.root / "docs" / "CLAIMS.md"),
                               "--tex", str(tex), "--json")
        data = json.loads(out)
        self.assertEqual(code, 1, out)          # 定理类没覆盖 = 错误
        self.assertEqual(sorted(data["tex"]["missing"]), ["thm:a", "thm:b"])

        (self.root / "docs" / "CLAIMS.md").write_text(
            CLAIMS + "| C2 | OPEN | 两条引理 | — | — | 对应 thm:a 与 thm:b |\n",
            encoding="utf-8")
        code, out, _ = run_cli("ledger", "--file", str(self.root / "docs" / "CLAIMS.md"),
                               "--tex", str(tex), "--json")
        self.assertEqual(code, 0, out)
        self.assertEqual(json.loads(out)["tex"]["missing"], [])

    def test_ledger_tex_missing_file(self):
        code, _, err = run_cli("ledger", "--file", str(self.root / "docs" / "CLAIMS.md"),
                               "--tex", str(self.tmp / "nope.tex"))
        self.assertEqual(code, 2)
        self.assertIn("找不到 tex", err)

    def test_ledger_missing_file(self):
        code, _, err = run_cli("ledger", "--file", str(self.tmp / "nope.md"))
        self.assertEqual(code, 2)
        self.assertIn("找不到台账", err)

    def test_upgrade(self):
        code, out, _ = run_cli("upgrade", "--root", str(self.root))
        self.assertEqual(code, 0, out)
        self.assertIn("1.0.0", out)

    def test_unknown_root_still_reports(self):
        code, out, err = run_cli("check", "--root", str(self.tmp / "nope"))
        self.assertEqual(code, 2)
        self.assertIn("库名", err + out)


if __name__ == "__main__":
    unittest.main()
