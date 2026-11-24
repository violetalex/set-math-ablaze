"""验收门禁：`mathlean check` 的实现。

四道门，缺一不可：
  1. build   —— `lake build` 通过；
  2. sorry   —— 源码里没有 sorry / admit（忽略注释与字符串）；
  3. axioms  —— `Audit.lean` 跑通，每个声明依赖的公理都在白名单内，
                自定义 `axiom` 全部登记；
  4. ledger  —— `docs/CLAIMS.md` 与源码、审计、依赖图一致。

任何一道门失败，退出码为 1。
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

from . import audit as audit_mod
from . import ledger as ledger_mod
from . import statements as statements_mod
from . import lean_scan
from . import docs_gate
from .config import Config

REQUIRED_DOCS = ("SPEC.md", "CLAIMS.md", "AUDIT.md")


@dataclass
class Result:
    name: str
    ok: bool
    summary: str
    details: List[str] = field(default_factory=list)
    duration: float = 0.0
    skipped: bool = False

    def to_dict(self) -> Dict[str, object]:
        return {
            "name": self.name,
            "ok": self.ok,
            "skipped": self.skipped,
            "summary": self.summary,
            "details": self.details,
            "duration": round(self.duration, 3),
        }


@dataclass
class Report:
    root: Path
    lib: str
    results: List[Result] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return all(r.ok or r.skipped for r in self.results)

    def add(self, r: Result) -> Result:
        self.results.append(r)
        return r

    def to_dict(self) -> Dict[str, object]:
        return {
            "root": str(self.root),
            "lib": self.lib,
            "ok": self.ok,
            "warnings": self.warnings,
            "results": [r.to_dict() for r in self.results],
        }


def _timed(name: str, fn) -> Result:
    t0 = time.time()
    try:
        res = fn()
    except Exception as exc:  # 门禁本身不能把整个检查搞崩
        res = Result(name, False, "检查脚本内部错误：{}: {}".format(type(exc).__name__, exc))
    res.duration = time.time() - t0
    return res


def check_build(cfg: Config, enabled: bool) -> Result:
    if not enabled:
        return Result("build", True, "已跳过（--no-build）", skipped=True)
    ok, text = audit_mod.build(cfg.root, cfg.timeout)
    if ok:
        return Result("build", True, "lake build 通过")
    lines = [l for l in text.splitlines() if l.strip()]
    return Result("build", False, "lake build 失败", lines[-40:])


def sources(cfg: Config) -> List[Path]:
    lib = cfg.lib or lean_scan.infer_lib(cfg.root)
    if not lib:
        return []
    return lean_scan.library_sources(cfg.root, lib)


def check_sorry(cfg: Config) -> Result:
    files = sources(cfg)
    if not files:
        return Result("sorry", False, "没有找到属于库 {} 的 .lean 文件".format(cfg.lib))
    findings, count = lean_scan.scan_files(files, cfg.root)
    if findings:
        kinds = sorted({f.token for f in findings})
        return Result("sorry", False,
                      "发现 {} 处 {}".format(len(findings), "/".join(kinds)),
                      [str(f) + "  ← " + f.text for f in findings])
    return Result("sorry", True,
                  "扫描 {} 个文件，无 {}".format(count, "/".join(lean_scan.DEFAULT_TOKENS)))


def check_axioms(cfg: Config, enabled: bool = True) -> Result:
    if not cfg.lib:
        return Result("axioms", False, "不知道库名，先设置 [project] lib")

    # 自定义 axiom 必须先登记（静态检查，不依赖编译，也不受 --no-audit 影响）
    custom_found: List[str] = []
    for p in sources(cfg):
        custom_found.extend(audit_mod.declared_axioms(
            p.read_text(encoding="utf-8", errors="replace")))
    unregistered = [a for a in custom_found
                    if a not in cfg.custom_axioms
                    and a.split(".")[-1] not in cfg.custom_axioms]
    if unregistered:
        return Result("axioms", False,
                      "未登记的自定义公理：{}".format(", ".join(sorted(set(unregistered)))),
                      ["在 mathlean.ini 的 [axioms] 段登记并写明论文中对应物"])

    if not enabled:
        return Result("axioms", True, "已跳过公理审计（--no-audit）", skipped=True)

    res = audit_mod.run(cfg.root, cfg.audit_file, cfg.timeout)
    if not res.ran or not res.ok:
        detail = [res.error] if res.error else []
        detail += res.tail().splitlines()
        return Result("axioms", False, "公理审计没跑通", detail)

    problems: List[str] = []
    allowed = set(cfg.allowed_names())
    for name, ax in sorted(res.axioms.items()):
        if "sorryAx" in ax:
            problems.append("{}：依赖 sorryAx".format(name))
        extra = ax - allowed
        if extra:
            problems.append("{}：依赖未登记公理 {}".format(name, ", ".join(sorted(extra))))
    if not res.axioms:
        problems.append("Audit.lean 没有产出任何 #print axioms 结果")
    if problems:
        return Result("axioms", False, "{} 个问题".format(len(problems)), problems)
    return Result("axioms", True,
                  "{} 个声明，公理 ⊆ {{{}}}".format(len(res.axioms), ", ".join(sorted(allowed))))


def check_statement(cfg: Config) -> Result:
    """陈述门：`Statements.lean` 里的 `Challenge.<名字>` 是否与声明的类型定义等价。

    没有挑战文件就跳过——这不是失败，只是说明这一层没有被独立重述过。
    """
    if not cfg.lib:
        return Result("statement", False, "不知道库名，先设置 [project] lib")
    res = statements_mod.run(cfg, cfg.timeout)
    if res.skipped:
        return Result("statement", True, res.error, skipped=True)
    if not res.ran:
        return Result("statement", False, res.error)
    if res.ok:
        return Result("statement", True,
                      "{} 条陈述与声明类型等价".format(len(res.compared)))
    return Result("statement", False, res.error, statements_mod.failures(res))


def check_ledger(cfg: Config, axiom_map: Optional[Dict[str, set]] = None) -> Result:
    if not cfg.claims_path.is_file():
        if cfg.strict_docs:
            return Result("ledger", False, "缺少 docs/CLAIMS.md")
        return Result("ledger", True, "没有 docs/CLAIMS.md，跳过", skipped=True)

    text = cfg.claims_path.read_text(encoding="utf-8", errors="replace")
    rows = ledger_mod.parse(text)
    if not rows:
        if cfg.strict_docs:
            return Result("ledger", False, "docs/CLAIMS.md 里没有解析到任何台账行")
        return Result("ledger", True, "台账为空（还没有命题）", skipped=True)

    decls: List[str] = []
    for p in sources(cfg):
        decls.extend(d.name for d in lean_scan.parse_lean_file(p, cfg.root))

    audit_path = cfg.audit_path
    audited = None  # None = 没有审计文件，跳过这项交叉检查
    if audit_path.is_file():
        audited = audit_mod.audited_names(
            audit_path.read_text(encoding="utf-8", errors="replace"))

    report = ledger_mod.validate(
        rows,
        decls=decls,
        audited_names=audited,
        axiom_map=axiom_map,
        allowed_axioms=cfg.allowed_names(),
    )
    details = [str(p) for p in report.problems]

    if not audit_path.is_file():
        details.append("WARNING: 缺少 {}，PROVED 行的审计交叉检查无法进行".format(cfg.audit_file))
    if report.errors:
        return Result("ledger", False, ledger_mod.summarize(report), details)
    return Result("ledger", True, ledger_mod.summarize(report), details)


def check_docs(cfg: Config) -> Result:
    # 文件存在不等于阶段做完了：脚手架把模板放进 docs/，模板带标记，算未填写。
    gone = docs_gate.missing(cfg.root, REQUIRED_DOCS)
    stub = [d for d in docs_gate.unfilled(cfg.root, REQUIRED_DOCS) if d not in gone]
    if not cfg.strict_docs:
        if gone or stub:
            parts = []
            if gone:
                parts.append("缺少 {}".format(", ".join(gone)))
            if stub:
                parts.append("{} 还是模板".format(", ".join(stub)))
            return Result("docs", True, "；".join(parts) + "（strict-docs 关闭）", skipped=True)
        return Result("docs", True, "阶段产物齐全")
    if gone:
        return Result("docs", False, "缺少 {}".format(", ".join(gone)))
    if stub:
        return Result("docs", False, "{} 还是脚手架模板，阶段没有真正产出".format(", ".join(stub)))
    return Result("docs", True, "阶段产物齐全")


def run(cfg: Config, build: bool = True, run_audit: bool = True) -> Report:
    rep = Report(root=cfg.root, lib=cfg.lib, warnings=list(cfg.warnings))

    rep.add(_timed("build", lambda: check_build(cfg, build)))
    rep.add(_timed("sorry", lambda: check_sorry(cfg)))
    ax = rep.add(_timed("axioms", lambda: check_axioms(cfg, run_audit)))

    axiom_map = None
    if run_audit and ax.ok and cfg.lib:
        res = audit_mod.run(cfg.root, cfg.audit_file, cfg.timeout)
        axiom_map = res.axioms if res.ran and res.ok else None
    rep.add(_timed("statement", lambda: check_statement(cfg)))
    rep.add(_timed("ledger", lambda: check_ledger(cfg, axiom_map)))
    rep.add(_timed("docs", lambda: check_docs(cfg)))
    return rep


def status(cfg: Config) -> Dict[str, object]:
    """`mathlean status` 用：文档、台账、审计的当前状态。"""
    docs = {}
    stubs = []
    for name in ("SPEC.md", "CITATIONS.md", "LEMMAS.md", "COUNTEREXAMPLES.md",
                 "AUDIT.md", "FORMALIZATION.md", "FIDELITY.md", "CLAIMS.md", "FINAL.md"):
        p = cfg.root / "docs" / name
        docs[name] = p.stat().st_size if p.is_file() else 0
        if p.is_file() and docs_gate.is_stub(p):
            stubs.append(name)

    rows = []
    if cfg.claims_path.is_file():
        rows = ledger_mod.parse(cfg.claims_path.read_text(encoding="utf-8", errors="replace"))
    counts = {s: 0 for s in ledger_mod.STATUSES}
    for r in rows:
        counts[r.status] = counts.get(r.status, 0) + 1

    runs_dir = cfg.root / "docs" / "RUNS"
    runs = sorted(p.name for p in runs_dir.glob("*.json")) if runs_dir.is_dir() else []

    return {
        "root": str(cfg.root),
        "lib": cfg.lib,
        "docs": docs,
        "stubs": stubs,
        "ledger": {"rows": len(rows), "counts": counts},
        "runs": runs,
        "has_audit": cfg.audit_path.is_file(),
        "has_config": cfg.exists,
    }
