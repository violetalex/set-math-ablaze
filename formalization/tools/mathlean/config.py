"""工程配置：`<root>/mathlean.ini`。

用 INI 而不是 TOML，是因为 macOS 自带 Python 3.9 没有 tomllib，
而这个工具要能在任何一台装了 Xcode 命令行工具的机器上直接跑。
"""

from __future__ import annotations

import configparser
import os
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

CONFIG_NAME = "mathlean.ini"
DEFAULT_ALLOWED = ("propext", "Classical.choice", "Quot.sound")
DEFAULT_MATHLIB = ".lake/packages/mathlib"

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")

TEMPLATE = """\
; mathlean 工程配置。`mathlean check` 读这个文件；删掉也能跑（用默认值）。

[project]
; Lean 库名，与 lakefile.toml 的 [[lean_lib]] name 一致
lib = {lib}

[lean]
; Mathlib 源码目录（路径依赖，不重新构建）
mathlib = {mathlib}
; 公理审计文件
audit = Audit.lean

[check]
; 是否运行 lake build
build = true
; 单个步骤超时（秒）
timeout = 1800
; 是否要求 docs 下的阶段产物齐全
strict-docs = false

[axioms]
; Lean 允许依赖的公理（白名单）
allowed = {allowed}
; 自定义公理必须登记，否则判为错误：登记名 = 论文中对应物
; mine = 论文引理 3.4 的假设
"""


@dataclass
class Config:
    root: Path
    lib: str = ""
    mathlib: str = ""
    audit_file: str = "Audit.lean"
    build: bool = True
    timeout: int = 1800
    strict_docs: bool = False
    allowed_axioms: List[str] = field(default_factory=lambda: list(DEFAULT_ALLOWED))
    custom_axioms: Dict[str, str] = field(default_factory=dict)
    warnings: List[str] = field(default_factory=list)
    exists: bool = False

    # ── 派生 ────────────────────────────────────────────────────────────
    @property
    def mathlib_path(self) -> Path:
        if not self.mathlib:
            return Path("")
        p = Path(os.path.expanduser(self.mathlib))
        # 相对路径按工程根目录解析，保证换一台机器也能跑
        return p if p.is_absolute() else self.root / p

    @property
    def audit_path(self) -> Path:
        return self.root / self.audit_file

    @property
    def claims_path(self) -> Path:
        return self.root / "docs" / "CLAIMS.md"

    def allowed_names(self) -> List[str]:
        return list(self.allowed_axioms) + list(self.custom_axioms.keys())


def _as_bool(value: str, default: bool, warn: List[str], key: str) -> bool:
    v = value.strip().lower()
    if v in ("1", "true", "yes", "on"):
        return True
    if v in ("0", "false", "no", "off"):
        return False
    warn.append("配置项 {} = {!r} 不是布尔值，按 {} 处理".format(key, value, default))
    return default


def _as_int(value: str, default: int, warn: List[str], key: str) -> int:
    try:
        n = int(value)
    except (TypeError, ValueError):
        warn.append("配置项 {} = {!r} 不是整数，按 {} 处理".format(key, value, default))
        return default
    if n <= 0:
        warn.append("配置项 {} 必须为正，按 {} 处理".format(key, default))
        return default
    return n


def _split_list(value: str) -> List[str]:
    return [x.strip() for x in re.split(r"[,\n]", value) if x.strip()]


def load(root: Path) -> Config:
    root = Path(root).resolve()
    cfg = Config(root=root, mathlib=os.environ.get("MATHLEAN_MATHLIB", DEFAULT_MATHLIB))
    path = root / CONFIG_NAME
    if not path.is_file():
        cfg.warnings.append("没有 {}，使用默认配置".format(CONFIG_NAME))
        return cfg

    parser = configparser.ConfigParser(interpolation=None)
    try:
        parser.read(path, encoding="utf-8")
    except configparser.Error as exc:
        cfg.warnings.append("{} 解析失败：{}".format(CONFIG_NAME, exc))
        return cfg
    cfg.exists = True

    if parser.has_section("project"):
        cfg.lib = parser.get("project", "lib", fallback="").strip()

    if parser.has_section("lean"):
        cfg.mathlib = parser.get("lean", "mathlib", fallback=cfg.mathlib).strip()
        cfg.audit_file = parser.get("lean", "audit", fallback="Audit.lean").strip()

    if parser.has_section("check"):
        cfg.build = _as_bool(parser.get("check", "build", fallback="true"),
                             True, cfg.warnings, "check.build")
        cfg.timeout = _as_int(parser.get("check", "timeout", fallback="1800"),
                              1800, cfg.warnings, "check.timeout")
        cfg.strict_docs = _as_bool(parser.get("check", "strict-docs", fallback="false"),
                                   False, cfg.warnings, "check.strict-docs")

    if parser.has_section("axioms"):
        for key, value in parser.items("axioms"):
            if key == "allowed":
                cfg.allowed_axioms = _split_list(value) or list(DEFAULT_ALLOWED)
            else:
                cfg.custom_axioms[key] = value.strip() or "（未写理由）"

    _validate(cfg)
    return cfg


def _validate(cfg: Config) -> None:
    if cfg.lib and not _IDENT.match(cfg.lib):
        cfg.warnings.append("库名 {!r} 不是合法标识符，已忽略".format(cfg.lib))
        cfg.lib = ""
    if not cfg.lib:
        from .lean_scan import infer_lib

        inferred = infer_lib(cfg.root)
        if inferred:
            cfg.lib = inferred
            cfg.warnings.append("配置里没有库名，从 lakefile 推断为 {!r}".format(inferred))
        else:
            cfg.warnings.append("推断不出库名，请设置 [project] lib")
    if cfg.mathlib:
        p = cfg.mathlib_path
        if not p.exists():
            cfg.warnings.append("Mathlib 路径不存在：{}".format(p))
