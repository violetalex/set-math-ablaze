import unittest

from mathlean import lean_scan


class StripCommentsTest(unittest.TestCase):
    def test_line_comment(self):
        src = "theorem a : True := by\n  -- sorry is fine here\n  trivial\n"
        self.assertNotIn("sorry", lean_scan.strip_comments(src))

    def test_block_comment_nested(self):
        src = "x /- outer /- inner sorry -/ still -/ y"
        out = lean_scan.strip_comments(src)
        self.assertNotIn("sorry", out)
        self.assertIn("x ", out)
        self.assertIn(" y", out)

    def test_string_literal_kept(self):
        src = 'def s := "-- not a comment"\n'
        out = lean_scan.strip_comments(src)
        self.assertIn("-- not a comment", out)

    def test_newlines_preserved(self):
        src = "/- a\nb\nc -/\nend\n"
        self.assertEqual(lean_scan.strip_comments(src).count("\n"), src.count("\n"))


class ScanTest(unittest.TestCase):
    def test_finds_sorry(self):
        found = lean_scan.scan_text("theorem t : True := by\n  sorry\n", "f.lean")
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].line, 2)

    def test_ignores_comments(self):
        src = "-- sorry\n/-\n admit\n-/\ntheorem t : True := trivial\n"
        self.assertEqual(lean_scan.scan_text(src, "f.lean"), [])

    def test_word_boundary(self):
        # `sorryAx` 不算 sorry —— 它是公理名，不是占位符
        self.assertEqual(lean_scan.scan_text("axiom sorryAx : False\n"), [])

    def test_trust_escapes_are_flagged(self):
        # 这些和 sorry 同类：都让 kernel 之外的东西参与判定
        for tok, src in [
            ("native_decide", "example : (1:Nat) = 1 := by\n  native_decide\n"),
            ("implemented_by", "@[implemented_by fast]\ndef slow : Nat := 0\n"),
            ("extern", "@[extern \"c_foo\"]\nopaque foo : Nat\n"),
        ]:
            found = lean_scan.scan_text(src, "f.lean")
            self.assertEqual([f.token for f in found], [tok], tok)

    def test_external_is_not_extern(self):
        # 词边界必须生效，否则 `external` 会误报
        self.assertEqual(lean_scan.scan_text("-- external link\ndef x := 1\n"), [])
        self.assertEqual(lean_scan.scan_text("def coexternal := 1\n"), [])

    def test_trust_escape_in_comment_ignored(self):
        src = "/- 我们不用 native_decide -/\ntheorem t : True := trivial\n"
        self.assertEqual(lean_scan.scan_text(src), [])

    def test_both_tokens_sorted(self):
        src = "admit\nsorry\n"
        found = lean_scan.scan_text(src)
        self.assertEqual([f.token for f in found], ["admit", "sorry"])


class DeclarationsTest(unittest.TestCase):
    def test_namespace_prefix(self):
        src = ("namespace Foo\n"
               "theorem a : True := trivial\n"
               "end Foo\n"
               "theorem b : True := trivial\n")
        names = [d.name for d in lean_scan.declarations(src)]
        self.assertEqual(names, ["Foo.a", "b"])

    def test_nested_namespace(self):
        src = ("namespace A\nnamespace B\nlemma c : True := trivial\n"
               "end B\nend A\n")
        names = [d.name for d in lean_scan.declarations(src)]
        self.assertEqual(names, ["A.B.c"])

    def test_axiom_kind(self):
        src = "axiom bad : False\n"
        d = lean_scan.declarations(src)[0]
        self.assertEqual(d.kind, "axiom")
        self.assertEqual(d.short, "bad")

    def test_ignores_commented_decl(self):
        src = "-- theorem ghost : True := trivial\n"
        self.assertEqual(lean_scan.declarations(src), [])

    def test_attributes_and_modifiers(self):
        src = "@[simp] protected theorem q : True := trivial\n"
        self.assertEqual([d.short for d in lean_scan.declarations(src)], ["q"])


if __name__ == "__main__":
    unittest.main()
