"""从骨架新建一个工程，以及把工具本身"贴"进工程（vendoring）。

每个工程自带一份 `tools/mathlean/`，因此：
  * 工程不依赖 ~/math-lean 是否存在；
  * 工程钉死的是创建时的检查器版本，结果可复现；
  * 升级用 `mathlean upgrade`，显式、可审计。
"""

from __future__ import annotations

import os
import re
import shutil
import stat
from pathlib import Path
from typing import List, Optional, Tuple

from . import __version__
from . import docs_gate
from .config import CONFIG_NAME, DEFAULT_ALLOWED, DEFAULT_MATHLIB, TEMPLATE

PKG_ROOT = Path(__file__).resolve().parent.parent
_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")

SKELETON_NAMES = ("lean", "skeleton")
TOOLS_DIR = "tools"

RUN_SHIM = '''\
#!/usr/bin/env python3
"""在工程内部运行 mathlean（不需要安装）。由 `mathlean new` 生成。"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from mathlean.cli import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
'''

CHECK_SH = '''\
#!/usr/bin/env bash
# 唯一验收口径。等价于 `mathlean check`。
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 -I tools/run_mathlean.py check "$@"
'''

GITIGNORE = '''\
.lake/
__pycache__/
*.pyc
.venv/
'''


class ScaffoldError(Exception):
    pass


def _skeleton_dir() -> Path:
    for name in SKELETON_NAMES:
        p = PKG_ROOT / name
        if (p / "lakefile.toml.in").is_file():
            return p
    raise ScaffoldError("找不到 Lean 骨架目录（{}）".format(PKG_ROOT))


def _templates_dir() -> Path:
    p = PKG_ROOT / "templates"
    if not p.is_dir():
        raise ScaffoldError("找不到模板目录 {}".format(p))
    return p


def _copy_tree_ignoring_cache(src: Path, dst: Path) -> None:
    shutil.copytree(src, dst, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc", ".DS_Store"))


def _merge_into(src: Path, dst: Path) -> None:
    """把 src 的内容并进已存在的 dst，然后删掉 src。"""
    dst.mkdir(parents=True, exist_ok=True)
    for item in src.iterdir():
        target = dst / item.name
        if item.is_dir():
            _merge_into(item, target)
        else:
            shutil.copy2(item, target)
    shutil.rmtree(src, ignore_errors=True)


def _substitute(path: Path, lib: str, mathlib: str) -> None:
    text = path.read_text(encoding="utf-8")
    new = (text.replace("__LIB_LC__", lib.lower())
               .replace("__LIB__", lib)
               .replace("__MATHLIB__", mathlib))
    if new != text:
        path.write_text(new, encoding="utf-8")


def vendor_tools(root: Path) -> Path:
    """把检查器、模板、骨架复制进 <root>/tools。返回 tools 目录。"""
    tools = root / TOOLS_DIR
    tools.mkdir(parents=True, exist_ok=True)

    pkg_dst = tools / "mathlean"
    src_pkg = Path(__file__).resolve().parent
    if pkg_dst.exists():
        shutil.rmtree(pkg_dst)
    _copy_tree_ignoring_cache(src_pkg, pkg_dst)

    tmpl_dst = tools / "templates"
    src_tmpl = _templates_dir()
    if tmpl_dst.exists():
        shutil.rmtree(tmpl_dst)
    _copy_tree_ignoring_cache(src_tmpl, tmpl_dst)

    skel_dst = tools / "skeleton"
    src_skel = _skeleton_dir()
    if skel_dst.exists():
        shutil.rmtree(skel_dst)
    _copy_tree_ignoring_cache(src_skel, skel_dst)

    shim = tools / "run_mathlean.py"
    shim.write_text(RUN_SHIM, encoding="utf-8")
    _make_executable(shim)

    (tools / "VERSION").write_text(__version__ + "\n", encoding="utf-8")
    return tools


def _make_executable(path: Path) -> None:
    mode = path.stat().st_mode
    path.chmod(mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def new_project(dest: Path, lib: str, mathlib: str = "", force: bool = False) -> Tuple[Path, List[str]]:
    """建工程。返回 (工程根, 提示信息)。"""
    dest = Path(dest).expanduser().resolve()
    notes: List[str] = []
    if not _IDENT.match(lib):
        raise ScaffoldError("库名 {!r} 不是合法 Lean 标识符".format(lib))
    if (dest / "lakefile.toml").exists() and not force:
        raise ScaffoldError("目标已经是一个 Lean 工程：{}（用 --force 覆盖）".format(dest))

    mathlib = os.path.expanduser(mathlib or DEFAULT_MATHLIB)
    if not Path(mathlib).is_dir():
        raise ScaffoldError(
            "找不到 Mathlib：{}\n传入第三个路径参数，或设置环境变量 MATHLEAN_MATHLIB".format(mathlib))

    dest.mkdir(parents=True, exist_ok=True)
    skel = _skeleton_dir()

    # 骨架 → 工程根
    for item in skel.iterdir():
        if item.name in ("scripts",):
            continue
        target = dest / item.name
        if item.is_dir():
            _copy_tree_ignoring_cache(item, target)
        else:
            shutil.copy2(item, target)

    # 占位名 → 真名
    top = dest / "__LIB__.lean"
    if top.exists():
        top.rename(dest / (lib + ".lean"))
    pkgdir = dest / "__LIB__"
    if pkgdir.exists():
        target_pkg = dest / lib
        if target_pkg.exists():      # --force 重建：合并进去，不 replace 整棵目录
            _merge_into(pkgdir, target_pkg)
        else:
            pkgdir.rename(target_pkg)
    lake = dest / "lakefile.toml.in"
    if lake.exists():
        lake.rename(dest / "lakefile.toml")

    for f in dest.rglob("*"):
        if f.is_file() and f.suffix in (".lean", ".toml", ".sh", ".md"):
            _substitute(f, lib, mathlib)

    # 工具与模板
    vendor_tools(dest)

    # 配置
    ini = dest / CONFIG_NAME
    if not ini.is_file():
        ini.write_text(TEMPLATE.format(lib=lib, mathlib=mathlib,
                                       allowed=", ".join(DEFAULT_ALLOWED)), encoding="utf-8")

    # 文档
    docs = dest / "docs"
    docs.mkdir(exist_ok=True)
    for t in _templates_dir().glob("*.md"):
        target = docs / t.name
        # --force 只覆盖"还没填"的模板，已经写过的阶段产物不动（重建工程不该毁掉工作）。
        if not target.exists() or (force and docs_gate.is_stub(target)):
            shutil.copy2(t, target)
    (docs / "RUNS").mkdir(exist_ok=True)

    # 脚本
    scripts = dest / "scripts"
    scripts.mkdir(exist_ok=True)
    check = scripts / "check.sh"
    check.write_text(CHECK_SH, encoding="utf-8")
    _make_executable(check)

    # 杂项
    gi = dest / ".gitignore"
    if not gi.exists():
        gi.write_text(GITIGNORE, encoding="utf-8")

    # 共用 Mathlib 构建产物（只链接 packages，不复制）
    lake_dir = dest / ".lake"
    lake_dir.mkdir(exist_ok=True)
    packages = lake_dir / "packages"
    shared = Path(mathlib).parent
    if not packages.exists() and shared.is_dir() and (shared / "mathlib").is_dir():
        try:
            packages.symlink_to(shared)
            notes.append("已链接共用包目录：{}".format(shared))
        except OSError as exc:
            notes.append("链接共用包目录失败（{}），首次构建会较慢".format(exc))

    return dest, notes


def upgrade(root: Path) -> str:
    """把工程里的 tools/ 更新到当前版本的检查器与模板。"""
    root = Path(root).expanduser().resolve()
    if not (root / "lakefile.toml").is_file():
        raise ScaffoldError("{} 不是 mathlean 工程".format(root))
    old = ""
    ver = root / TOOLS_DIR / "VERSION"
    if ver.is_file():
        old = ver.read_text(encoding="utf-8").strip()
    vendor_tools(root)
    return "{} → {}（{}）".format(old or "未安装", __version__, root / TOOLS_DIR)
