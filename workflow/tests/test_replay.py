import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from mathlean import replay


def _project(root: Path, lib: str = "Foo", entry: bool = True):
    (root / lib).mkdir()
    (root / lib / "A.lean").write_text("", encoding="utf-8")
    if entry:
        (root / (lib + ".lean")).write_text("", encoding="utf-8")
    return root


class EntryModulesTest(unittest.TestCase):
    def test_prefers_entry_module(self):
        with tempfile.TemporaryDirectory() as d:
            root = _project(Path(d))
            # leanchecker 会顺着 import 图检查依赖，只跑入口就够
            self.assertEqual(replay.entry_modules(root, "Foo"), ["Foo"])

    def test_falls_back_to_all_modules(self):
        with tempfile.TemporaryDirectory() as d:
            root = _project(Path(d), entry=False)
            self.assertEqual(replay.entry_modules(root, "Foo"), ["Foo.A"])


class MathlibRevTest(unittest.TestCase):
    def test_reads_manifest(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "lake-manifest.json").write_text(json.dumps({
                "packages": [
                    {"name": "batteries", "rev": "aaa"},
                    {"name": "mathlib", "rev": "d13f23b7"},
                ]}), encoding="utf-8")
            self.assertEqual(replay.mathlib_rev(root), "d13f23b7")

    def test_missing_or_broken_manifest(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.assertEqual(replay.mathlib_rev(root), "")
            (root / "lake-manifest.json").write_text("{not json", encoding="utf-8")
            self.assertEqual(replay.mathlib_rev(root), "")


class RunTest(unittest.TestCase):
    def test_success(self):
        with tempfile.TemporaryDirectory() as d:
            root = _project(Path(d))
            ok = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
            with mock.patch("mathlean.replay.shutil.which", return_value="/usr/bin/lake"), \
                 mock.patch("mathlean.replay.subprocess.run", return_value=ok):
                res = replay.run(_cfg(root, "Foo"))
            self.assertTrue(res.ran)
            self.assertTrue(res.ok)
            self.assertEqual([m.module for m in res.modules], ["Foo"])

    def test_rejection_is_failure_and_keeps_output(self):
        with tempfile.TemporaryDirectory() as d:
            root = _project(Path(d))
            bad = subprocess.CompletedProcess(
                args=[], returncode=1, stdout="", stderr="declaration not accepted")
            with mock.patch("mathlean.replay.shutil.which", return_value="/usr/bin/lake"), \
                 mock.patch("mathlean.replay.subprocess.run", return_value=bad):
                res = replay.run(_cfg(root, "Foo"))
            self.assertFalse(res.ok)
            self.assertEqual([m.module for m in res.failed()], ["Foo"])
            self.assertIn("not accepted", "\\n".join(replay.summary_lines(res)))

    def test_missing_lake(self):
        with tempfile.TemporaryDirectory() as d:
            root = _project(Path(d))
            with mock.patch("mathlean.replay.shutil.which", return_value=None):
                res = replay.run(_cfg(root, "Foo"))
            self.assertFalse(res.ran)
            self.assertIn("lake", res.error)


def _cfg(root: Path, lib: str = "Foo"):
    from mathlean.config import Config
    return Config(root=root, lib=lib)


if __name__ == "__main__":
    unittest.main()
