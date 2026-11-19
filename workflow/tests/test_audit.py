import unittest

from mathlean import audit


class ParseAxiomsTest(unittest.TestCase):
    def test_depends(self):
        out = "'Foo.bar' depends on axioms: [propext, Classical.choice]\n"
        self.assertEqual(audit.parse_axioms(out), {"Foo.bar": {"propext", "Classical.choice"}})

    def test_no_axioms(self):
        out = "'Foo.baz' does not depend on any axioms\n"
        self.assertEqual(audit.parse_axioms(out), {"Foo.baz": set()})

    def test_sorry_ax(self):
        out = "'Foo.q' depends on axioms: [sorryAx, propext]\n"
        self.assertIn("sorryAx", audit.parse_axioms(out)["Foo.q"])

    def test_unquoted(self):
        out = "Foo.q depends on axioms: [propext]\n"
        self.assertEqual(audit.parse_axioms(out), {"Foo.q": {"propext"}})

    def test_noise_ignored(self):
        out = "info: building\nwarning: unused variable\n"
        self.assertEqual(audit.parse_axioms(out), {})

    def test_multiple_lines_merge(self):
        out = ("'A.x' depends on axioms: [propext]\n"
               "'A.x' depends on axioms: [Classical.choice]\n")
        self.assertEqual(audit.parse_axioms(out)["A.x"], {"propext", "Classical.choice"})


class DeclaredAxiomsTest(unittest.TestCase):
    def test_finds_axiom(self):
        self.assertEqual(audit.declared_axioms("axiom foo : False\n"), ["foo"])

    def test_ignores_comment(self):
        self.assertEqual(audit.declared_axioms("-- axiom foo : False\n"), [])

    def test_ignores_sorryax_string(self):
        self.assertEqual(audit.declared_axioms("def s := \"axiom x\"\n"), [])


class AuditedNamesTest(unittest.TestCase):
    def test_print_axioms(self):
        text = "#print axioms Foo.bar\n-- #print axioms Gone\n"
        self.assertEqual(audit.audited_names(text), {"Foo.bar"})


if __name__ == "__main__":
    unittest.main()
