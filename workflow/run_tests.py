#!/usr/bin/env python3
"""跑测试：`python3 run_tests.py [-v]`。

必须自己把仓库根目录插进 sys.path —— 用 `python3 -I` 时它不会自动加。
"""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def main() -> int:
    verbose = "-v" in sys.argv
    pattern = "test_*.py"
    for arg in sys.argv[1:]:
        if arg.startswith("test_"):
            pattern = arg
    suite = unittest.TestLoader().discover(
        os.path.join(HERE, "tests"), pattern=pattern, top_level_dir=HERE)
    result = unittest.TextTestRunner(verbosity=2 if verbose else 1).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
