"""docs 门：阶段产物是否真的被填写过。

脚手架会把 SPEC/CLAIMS/AUDIT 的模板放进 docs/，所以"文件存在"不等于"阶段做完了"。
模板首行带 `<!-- mathlean:template -->` 标记，含该标记的文件算**未填写**。
"""

from __future__ import annotations

from pathlib import Path
from typing import List

MARK = "<!-- mathlean:template"
REQUIRED = ("SPEC.md", "CLAIMS.md", "AUDIT.md")


def is_stub(path: Path) -> bool:
    """不存在，或者还是模板（含标记）都算没填。"""
    if not path.is_file():
        return True
    try:
        head = path.read_text(encoding="utf-8", errors="replace")[:2000]
    except OSError:
        return True
    return MARK in head


def unfilled(root: Path, required=REQUIRED) -> List[str]:
    docs = root / "docs"
    return [d for d in required if is_stub(docs / d)]


def missing(root: Path, required=REQUIRED) -> List[str]:
    return [d for d in required if not (root / "docs" / d).is_file()]
