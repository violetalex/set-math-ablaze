#!/usr/bin/env python3
"""在工程内部运行 mathlean（不需要安装）。由 `mathlean new` 生成。"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from mathlean.cli import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
