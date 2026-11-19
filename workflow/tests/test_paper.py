import unittest

from mathlean import paper

TEX = r"""
\begin{theorem}[swirl-free; {\cite[Theorem~5.2]{KNSS}}]\label{thm:knss}
x
\end{theorem}

\begin{hypothesis}[$(H_1)$]\label{hyp:main}
y
\end{hypothesis}

\begin{remark}[no label here]
z
\end{remark}

\begin{remark}[merged]\label{rem:merged}
w
\end{remark}
"""


class EnvironmentsTest(unittest.TestCase):
    def test_nested_optional_arg(self):
        envs = paper.environments(TEX)
        self.assertEqual(envs[0].kind, "theorem")
        self.assertEqual(envs[0].label, "thm:knss")

    def test_kinds_and_labels(self):
        envs = paper.environments(TEX)
        self.assertEqual([e.kind for e in envs],
                         ["theorem", "hypothesis", "remark", "remark"])
        self.assertEqual([e.label for e in envs], ["thm:knss", "hyp:main", "", "rem:merged"])

    def test_line_numbers(self):
        envs = paper.environments(TEX)
        self.assertEqual(envs[0].line, 2)


class CoverageTest(unittest.TestCase):
    def test_missing_and_covered(self):
        ledger_text = "见 thm:knss；hyp:main 是全表前提"
        missing, covered, unlabeled = paper.coverage(TEX, ledger_text)
        self.assertEqual([e.label for e in covered], ["thm:knss", "hyp:main"])
        self.assertEqual([e.label for e in missing], ["rem:merged"])
        self.assertEqual(len(unlabeled), 1)

    def test_substring_does_not_match_prefix(self):
        # thm:knss 不能因为台账里出现 thm:knss2 就算覆盖
        missing, _, _ = paper.coverage(TEX, "thm:knss2")
        self.assertTrue(any(e.label == "thm:knss" for e in missing))

    def test_summary(self):
        _, covered, unlabeled = paper.coverage(TEX, "thm:knss hyp:main rem:merged")
        text = paper.summarize([], covered, unlabeled)
        self.assertIn("无 label 1", text)


if __name__ == "__main__":
    unittest.main()
