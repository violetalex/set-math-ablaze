"""命令行入口：`mathlean <子命令>`。"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import List, Optional

from . import __version__
from . import checks, doctor, selfcheck
from . import ledger as ledger_mod
from . import paper as paper_mod
from .config import CONFIG_NAME, load
from .scaffold import ScaffoldError, new_project, upgrade

GREEN, RED, YELLOW, DIM, RESET = (
    ("\033[32m", "\033[31m", "\033[33m", "\033[2m", "\033[0m")
    if sys.stdout.isatty() else ("", "", "", "", "")
)


def find_root(start: Optional[str]) -> Path:
    if start:
        return Path(start).expanduser().resolve()
    cur = Path.cwd().resolve()
    for p in [cur] + list(cur.parents):
        if (p / "lakefile.toml").is_file() or (p / CONFIG_NAME).is_file():
            return p
    return cur


def _mark(ok: bool, skipped: bool = False) -> str:
    if skipped:
        return YELLOW + "·" + RESET
    return (GREEN + "✔" + RESET) if ok else (RED + "✘" + RESET)


def cmd_check(args) -> int:
    root = find_root(args.root)
    cfg = load(root)
    if args.strict_docs:
        cfg.strict_docs = True
    if not cfg.lib:
        print("错误：不知道库名。在 {} 里设置 [project] lib。".format(CONFIG_NAME), file=sys.stderr)
        return 2

    rep = checks.run(cfg, build=not args.no_build, run_audit=not args.no_audit)

    if args.json:
        print(json.dumps(rep.to_dict(), ensure_ascii=False, indent=2))
        return 0 if rep.ok else 1

    if not args.quiet:
        print("mathlean {}   {}   (库 {})".format(__version__, root, cfg.lib))
        for w in rep.warnings:
            print("  {} {}".format(YELLOW + "!" + RESET, w))
        print()

    width = max(len(r.name) for r in rep.results)
    for r in rep.results:
        print("{} {:<{w}} {:>6.2f}s  {}".format(
            _mark(r.ok, r.skipped), r.name, r.duration, r.summary, w=width))
        if r.details and (not r.ok or args.verbose):
            for d in r.details[: (40 if r.ok else 60)]:
                print("     " + DIM + d + RESET, )

    if rep.ok:
        if not args.quiet:
            print("\n" + GREEN + "OK" + RESET)
        return 0
    bad = [r.name for r in rep.results if not r.ok and not r.skipped]
    print("\n" + RED + "失败" + RESET + "：{}".format(", ".join(bad)))
    return 1


def cmd_new(args) -> int:
    try:
        dest, notes = new_project(Path(args.dest), args.lib, args.mathlib or "",
                                  force=args.force)
    except ScaffoldError as exc:
        print("错误：{}".format(exc), file=sys.stderr)
        return 1
    print("已创建 {}".format(dest))
    for n in notes:
        print("  " + n)
    print("""
下一步：
  1. 写 {d}/docs/SPEC.md        （对象、假设、结论、可伪性）
  2. 写 {d}/docs/CLAIMS.md      （命题台账）
  3. 在 {d}/{lib}/ 下写 Lean
  4. bash {d}/scripts/check.sh  验收
""".format(d=dest, lib=args.lib))
    return 0


def cmd_upgrade(args) -> int:
    try:
        print(upgrade(find_root(args.root)))
    except ScaffoldError as exc:
        print("错误：{}".format(exc), file=sys.stderr)
        return 1
    return 0


def cmd_status(args) -> int:
    root = find_root(args.root)
    cfg = load(root)
    info = checks.status(cfg)

    if args.json:
        print(json.dumps(info, ensure_ascii=False, indent=2))
        return 0

    print("工程   {}".format(info["root"]))
    print("库     {}".format(info["lib"] or "（未知）"))
    print("配置   {}".format("mathlean.ini" if info["has_config"] else "无（默认值）"))
    print("审计   {}".format("有" if info["has_audit"] else "无"))
    print()
    print("阶段产物")
    for name, size in info["docs"].items():
        stub = name in info.get("stubs", [])
        mark = DIM + "·" + RESET if (not size or stub) else GREEN + "✔" + RESET
        note = "缺" if not size else ("{} 字节（模板，未填写）".format(size) if stub
                                      else "{} 字节".format(size))
        print("  {} {:<20} {}".format(mark, name, note))
    print()
    ledger = info["ledger"]
    print("台账   {} 条".format(ledger["rows"]))
    for status, n in ledger["counts"].items():
        if n:
            print("  {:<16} {}".format(status, n))
    if info["runs"]:
        print("\n运行记录 {}".format("、".join(info["runs"][-5:])))
    return 0


def cmd_ledger(args) -> int:
    """独立检查一份台账 —— 不需要 Lean 工程，论文审计用。"""
    if args.file:
        path = Path(args.file).expanduser()
    else:
        path = load(find_root(args.root)).claims_path
    if not path.is_file():
        print("错误：找不到台账 {}".format(path), file=sys.stderr)
        return 2

    rows = ledger_mod.parse(path.read_text(encoding="utf-8", errors="replace"))
    report = ledger_mod.validate(rows, decls=(), audited_names=None)
    for r in rows:
        if r.status == "PROVED":
            report.warn(r.id, "标了 PROVED 但没有 Lean 工程；本命令不验证声明是否存在")

    cov = None
    if args.tex:
        tex_path = Path(args.tex).expanduser()
        if not tex_path.is_file():
            print("错误：找不到 tex {}".format(tex_path), file=sys.stderr)
            return 2
        missing, covered, unlabeled = paper_mod.coverage(
            paper_mod.read_tex(tex_path),
            path.read_text(encoding="utf-8", errors="replace"))
        cov = {
            "file": str(tex_path),
            "covered": len(covered),
            "missing": [e.label for e in missing if e.label],
            "unlabeled": len(unlabeled),
        }
        for e in missing:
            where = "{}:{} ({})".format(tex_path.name, e.line, e.kind)
            if e.kind in paper_mod.STRICT_ENVS:
                report.error(e.label, "台账里没有引用 {}，定理类环境必须覆盖".format(where))
            else:
                report.warn(e.label, "台账里没有引用 {}；若已合并进别的行，请在备注写明".format(where))

    if args.json:
        out = {
            "file": str(path),
            "rows": len(rows),
            "counts": report.counts(),
            "problems": [p.__dict__ for p in report.problems],
        }
        if cov:
            out["tex"] = cov
        print(json.dumps(out, ensure_ascii=False, indent=2))
        return 1 if report.errors else 0

    print("{}    {}".format(path, ledger_mod.summarize(report)))
    if cov:
        print("{}{}".format(" " * len(str(path)) + "    ",
                            "tex {}：覆盖 {} 个 label，缺 {} 个，无 label {} 个".format(
                                Path(cov["file"]).name, cov["covered"],
                                len(cov["missing"]), cov["unlabeled"])))
    if args.list:
        print()
        for r in rows:
            print("  {:<4} {:<17} {:<40} {}".format(
                r.id, r.status, r.statement[:40], r.lean if not ledger_mod.is_placeholder(r.lean) else ""))
    if report.problems:
        print()
        for p in report.problems:
            color = RED if p.level == "error" else YELLOW
            print("{} {}: {}{}".format(color + p.level.upper() + RESET, p.where, p.message, ""))
    return 1 if report.errors else 0


def cmd_doctor(args) -> int:
    root = find_root(args.root)
    cfg = load(root)
    items = doctor.check(cfg)
    if args.json:
        print(json.dumps([i.__dict__ for i in items], ensure_ascii=False, indent=2))
        return 0 if doctor.worst(items) != doctor.FAIL else 1
    for i in items:
        color = {doctor.OK: GREEN, doctor.WARN: YELLOW, doctor.FAIL: RED}[i.status]
        print("{}{:<4}{} {:<16} {}".format(color, i.status, RESET, i.name, i.detail))
        if i.fix and i.status != doctor.OK:
            print("     " + DIM + "→ " + i.fix + RESET)
    return 0 if doctor.worst(items) != doctor.FAIL else 1


def cmd_selfcheck(args) -> int:
    results, ok = selfcheck.run(keep=args.keep, with_lean=args.with_lean)
    for r in results:
        print("{} {:<28} {}".format(_mark(r["ok"]), r["scenario"], r["detail"]))
    print()
    if ok:
        print(GREEN + "自检通过" + RESET + "：{} 个场景都按预期工作".format(len(results)))
        return 0
    print(RED + "自检失败" + RESET + "：门禁的行为与预期不一致")
    return 1


def cmd_version(args) -> int:
    print("mathlean {}".format(__version__))
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="mathlean",
        description="数学命题求解 + Lean 4 机器验证工作流的确定性部分。",
        epilog="需要判断的部分（证明、反例、审计）由 workflow.js 编排 agent 完成。",
    )
    sub = p.add_subparsers(dest="command", required=True)

    q = sub.add_parser("check", help="跑验收门禁（唯一验收口径）")
    q.add_argument("--root", help="工程目录（默认从当前目录向上找）")
    q.add_argument("--no-build", action="store_true", help="跳过 lake build")
    q.add_argument("--no-audit", action="store_true", help="跳过公理审计（自定义公理检查仍会跑）")
    q.add_argument("--strict-docs", action="store_true", help="要求 docs 下阶段产物齐全")
    q.add_argument("--json", action="store_true", help="输出 JSON")
    q.add_argument("--quiet", action="store_true", help="少打点字")
    q.add_argument("--verbose", action="store_true", help="通过的检查也打印细节")
    q.set_defaults(func=cmd_check)

    n = sub.add_parser("new", help="从骨架新建工程")
    n.add_argument("dest")
    n.add_argument("lib")
    n.add_argument("--mathlib", help="Mathlib 源码目录")
    n.add_argument("--force", action="store_true", help="覆盖已有工程")
    n.set_defaults(func=cmd_new)

    u = sub.add_parser("upgrade", help="把工程的 tools/ 更新到当前版本")
    u.add_argument("--root")
    u.set_defaults(func=cmd_upgrade)

    lg = sub.add_parser("ledger", help="检查一份台账（不需要 Lean 工程）")
    lg.add_argument("--file", help="台账路径（默认 <工程>/docs/CLAIMS.md）")
    lg.add_argument("--tex", help="同时核对论文 tex 里的定理环境是否都被台账覆盖")
    lg.add_argument("--root", help="工程目录")
    lg.add_argument("--list", action="store_true", help="逐条列出")
    lg.add_argument("--json", action="store_true")
    lg.set_defaults(func=cmd_ledger)

    s = sub.add_parser("status", help="看工程当前状态")
    s.add_argument("--root")
    s.add_argument("--json", action="store_true")
    s.set_defaults(func=cmd_status)

    d = sub.add_parser("doctor", help="环境体检")
    d.add_argument("--root")
    d.add_argument("--json", action="store_true")
    d.set_defaults(func=cmd_doctor)

    sc = sub.add_parser("selfcheck", help="验证门禁本身是否按预期工作")
    sc.add_argument("--with-lean", action="store_true", help="连编译与公理审计一起验")
    sc.add_argument("--keep", action="store_true", help="保留临时工程")
    sc.set_defaults(func=cmd_selfcheck)

    v = sub.add_parser("version", help="版本号")
    v.set_defaults(func=cmd_version)
    return p


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv if argv is not None else sys.argv[1:])
    try:
        return args.func(args)
    except KeyboardInterrupt:
        print("\n中断", file=sys.stderr)
        return 130
