import unittest

from mathlean import ledger

HEADER = "| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |\n|---|---|---|---|---|---|\n"


def doc(*rows):
    return HEADER + "".join(r + "\n" for r in rows)


class ParseTest(unittest.TestCase):
    def test_basic(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | 说明 |"))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].id, "C1")
        self.assertEqual(rows[0].status, "PROVED")
        self.assertEqual(rows[0].lean, "Foo.a")

    def test_fenced_block_ignored(self):
        text = doc("| C1 | OPEN | 甲 | — | — | 待定 |") + "\n```\n| C2 | PROVED | 乙 | x | — | — |\n```\n"
        self.assertEqual([r.id for r in ledger.parse(text)], ["C1"])

    def test_escaped_pipe(self):
        rows = ledger.parse(doc(r"| C1 | OPEN | a \| b | — | — | 备注 |"))
        self.assertEqual(rows[0].statement, "a | b")

    def test_placeholder_row_skipped(self):
        rows = ledger.parse(doc("| _ | OPEN | 占位 | — | — | — |"))
        self.assertEqual(rows, [])

    def test_deps_parsing(self):
        rows = ledger.parse(doc("| C3 | OPEN | 甲 | — | C1、C2 | 卡住 |"))
        self.assertEqual(rows[0].deps, ["C1", "C2"])

    def test_deps_placeholder(self):
        rows = ledger.parse(doc("| C1 | OPEN | 甲 | — | — | 卡住 |"))
        self.assertEqual(rows[0].deps, [])


class ValidateTest(unittest.TestCase):
    def test_clean_proved(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | — |"))
        rep = ledger.validate(rows, decls=["Foo.a"], audited_names=["Foo.a"])
        self.assertEqual(rep.errors, [])

    def test_proved_missing_decl(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | — |"))
        rep = ledger.validate(rows, decls=["Bar.b"], audited_names=["Foo.a"])
        self.assertTrue(any("找不到声明" in str(e) for e in rep.errors))

    def test_proved_missing_audit(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | — |"))
        # None = 没有审计文件 → 跳过；有文件但没这一条 → 报错
        self.assertEqual(ledger.validate(rows, decls=["Foo.a"], audited_names=None).errors, [])
        rep = ledger.validate(rows, decls=["Foo.a"], audited_names=[])
        self.assertTrue(any("没有 #print axioms" in str(e) for e in rep.errors))
        rep = ledger.validate(rows, decls=["Foo.a"], audited_names=["Bar.b"])
        self.assertTrue(any("没有 #print axioms" in str(e) for e in rep.errors))

    def test_conditional_needs_hypothesis(self):
        rows = ledger.parse(doc("| C1 | CONDITIONAL | 甲 | — | — | 在某条件下 |"))
        rep = ledger.validate(rows)
        self.assertTrue(any("假设" in str(e) for e in rep.errors))
        rows = ledger.parse(doc("| C1 | CONDITIONAL | 甲 | — | — | 假设：ρ>0 |"))
        self.assertEqual(ledger.validate(rows).errors, [])

    def test_refuted_needs_counterexample(self):
        rows = ledger.parse(doc("| C1 | REFUTED | 甲 | — | — | 数值上不成立 |"))
        self.assertTrue(ledger.validate(rows).errors)

    def test_cited_needs_identifier(self):
        rows = ledger.parse(doc("| C1 | CITED | 甲 | — | — | 来自 KNSS |"))
        self.assertTrue(any("引用" in str(e) for e in ledger.validate(rows).errors))
        rows = ledger.parse(doc("| C1 | CITED | 甲 | — | — | 引用：KNSS Thm 5.2 |"))
        self.assertEqual(ledger.validate(rows).errors, [])

    def test_bad_status(self):
        rows = ledger.parse(doc("| C1 | MAYBE | 甲 | — | — | — |"))
        self.assertTrue(any("非法状态" in str(e) for e in ledger.validate(rows).errors))

    def test_duplicate_id(self):
        rows = ledger.parse(doc("| C1 | OPEN | 甲 | — | — | a |",
                                "| C1 | OPEN | 乙 | — | — | b |"))
        self.assertTrue(any("重复" in str(e) for e in ledger.validate(rows).errors))

    def test_dependency_cycle(self):
        rows = ledger.parse(doc("| C1 | OPEN | 甲 | — | C2 | a |",
                                "| C2 | OPEN | 乙 | — | C1 | b |"))
        rep = ledger.validate(rows)
        self.assertTrue(any("环" in str(e) for e in rep.errors))

    def test_missing_dependency(self):
        rows = ledger.parse(doc("| C1 | OPEN | 甲 | — | C9 | a |"))
        self.assertTrue(any("不在台账" in str(e) for e in ledger.validate(rows).errors))

    def test_sorry_axiom_is_error(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | — |"))
        rep = ledger.validate(rows, decls=["Foo.a"], audited_names=["Foo.a"],
                              axiom_map={"Foo.a": {"sorryAx"}}, allowed_axioms=["propext"])
        self.assertTrue(any("sorryAx" in str(e) for e in rep.errors))

    def test_unregistered_axiom_is_error(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | — |"))
        rep = ledger.validate(rows, decls=["Foo.a"], audited_names=["Foo.a"],
                              axiom_map={"Foo.a": {"mine"}}, allowed_axioms=["propext"])
        self.assertTrue(any("未登记" in str(e) for e in rep.errors))

    def test_registered_axiom_passes(self):
        rows = ledger.parse(doc("| C1 | PROVED | 甲 | Foo.a | — | — |"))
        rep = ledger.validate(rows, decls=["Foo.a"], audited_names=["Foo.a"],
                              axiom_map={"Foo.a": {"mine"}}, allowed_axioms=["propext", "mine"])
        self.assertEqual(rep.errors, [])


class SplitRowTest(unittest.TestCase):
    def test_escaped(self):
        self.assertEqual(ledger.split_row(r"| a \| b | c |"), ["a | b", "c"])

    def test_empty_cells(self):
        self.assertEqual(ledger.split_row("| a |  | c |"), ["a", "", "c"])


if __name__ == "__main__":
    unittest.main()
