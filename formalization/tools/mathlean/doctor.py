"""环境体检：`mathlean doctor`。

把"为什么跑不起来"分成可执行的几条，而不是让人对着一屏报错猜。
"""

from __future__ import annotations

import os
import platform
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional

from . import __version__
from . import audit as audit_mod
from .config import Config

OK, WARN, FAIL = "OK", "WARN", "FAIL"


@dataclass
class Item:
    status: str
    name: str
    detail: str
    fix: str = ""


def _run(cmd: List[str], cwd: Optional[Path] = None) -> Optional[str]:
    """跑一条命令，返回第一行非空输出；失败返回 None。

    `lake --version` 需要在工程目录里跑，否则会说没有默认 toolchain。
    """
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60,
                              cwd=str(cwd) if cwd else None, env=audit_mod.lean_env())
    except (OSError, subprocess.TimeoutExpired):
        return None
    lines = [l.strip() for l in ((proc.stdout or "") + (proc.stderr or "")).splitlines() if l.strip()]
    if proc.returncode != 0:
        return None
    return lines[0] if lines else ""


def check(cfg: Config) -> List[Item]:
    items: List[Item] = []

    v = sys.version_info
    if v >= (3, 9):
        items.append(Item(OK, "Python", "{}.{}.{}".format(*v[:3])))
    else:
        items.append(Item(FAIL, "Python", "{}.{}.{}".format(*v[:3]), "需要 3.9 及以上"))

    items.append(Item(OK, "平台", "{} {}".format(platform.system(), platform.machine())))

    elan = audit_mod.elan_bin()
    if elan:
        items.append(Item(OK, "elan", str(elan)))
    else:
        items.append(Item(FAIL, "elan", "找不到 ~/.elan/bin", "curl https://elan.lean-lang.org 安装"))

    lake = shutil.which("lake", path=str(elan)) if elan else shutil.which("lake")
    if lake:
        ver = _run([lake, "--version"], cwd=cfg.root) or ""
        if ver:
            items.append(Item(OK, "lake", ver))
        else:
            items.append(Item(WARN, "lake", "执行了但没拿到版本号",
                              "在工程目录里跑一次 lake --version 看看"))
    else:
        items.append(Item(FAIL, "lake", "PATH 里没有", "安装 elan 后重开终端"))

    toolchain = cfg.root / "lean-toolchain"
    if toolchain.is_file():
        items.append(Item(OK, "lean-toolchain", toolchain.read_text(encoding="utf-8").strip()))
    else:
        items.append(Item(WARN, "lean-toolchain", "缺这个文件，lake 会用默认版本",
                          "从别的工程复制一份"))

    if not cfg.mathlib:
        items.append(Item(FAIL, "Mathlib", "没有配置路径", "在 mathlean.ini 里设 [lean] mathlib"))
    else:
        p = cfg.mathlib_path
        if p.is_dir() and (p / "Mathlib").is_dir():
            items.append(Item(OK, "Mathlib", str(p)))
        else:
            items.append(Item(FAIL, "Mathlib", "不存在或不是 Mathlib 源码：{}".format(p),
                              "改 mathlean.ini 的 [lean] mathlib"))

    packages = cfg.root / ".lake" / "packages"
    if packages.is_symlink():
        items.append(Item(OK, ".lake/packages", "→ {}".format(os.readlink(packages))))
    elif packages.is_dir():
        items.append(Item(OK, ".lake/packages", "本地目录（首次构建会比较慢）"))
    else:
        items.append(Item(WARN, ".lake/packages", "不存在",
                          "mathlean new 会自动链接共用包目录"))

    if cfg.lib:
        items.append(Item(OK, "库名", cfg.lib))
    else:
        items.append(Item(FAIL, "库名", "未知", "在 mathlean.ini 设置 [project] lib"))

    if cfg.exists:
        items.append(Item(OK, "配置", str(cfg.root / "mathlean.ini")))
    else:
        items.append(Item(WARN, "配置", "没有 mathlean.ini，用默认值", "mathlean new 会生成"))

    for w in cfg.warnings:
        items.append(Item(WARN, "配置警告", w))

    audit_file = cfg.audit_path
    if audit_file.is_file():
        items.append(Item(OK, "审计文件", cfg.audit_file))
    else:
        items.append(Item(WARN, "审计文件", "找不到 {}".format(cfg.audit_file),
                          "写一个只含 #print axioms 的 .lean 文件"))

    items.append(Item(OK, "mathlean", __version__))
    return items


def worst(items: List[Item]) -> str:
    if any(i.status == FAIL for i in items):
        return FAIL
    if any(i.status == WARN for i in items):
        return WARN
    return OK
