# 更新记录

## 未发布

**新增**

- `statement` 门（第六道）：工程根放 `Statements.lean`，用 `namespace Challenge` 独立
  重写每个 `PROVED` 命题；门禁把声明类型与它做定义等价比较。只比类型，不读证明。
  没有 `Statements.lean` 时跳过。
- `mathlean frontier`：算**审计面**。从台账的 `PROVED` 行出发，沿项目内部声明做传递闭包，
  收集它们直接从 Mathlib/Init 借来的常量，按「公理 / 数学定理 / 策略支撑 / 定义与实例 /
  语言基础」分类。`--write` 写出 markdown，`--json` 给机器读，`--target` 指定声明。
  只读报告，不参与退出码。
- `mathlean replay`：用 `leanchecker` 读编译产物、不经 elaborator 把每个模块重新交给 kernel
  检查。`build` 走 elaborator，replay 只走 kernel；对 `addDecl` / `kexactB` 这类绕过
  elaborator 的构造是唯一有效的检查。`--checker` 预留了接独立实现的口子。
- 骨架新增 `tools/skeleton/Frontier.lean`（`mathlean new` 会带上）。
- 18 个单元测试（`tests/test_frontier.py` 11 个、`tests/test_statements.py` 7 个），总计 100。

**修正**

- `DEFAULT_MATHLIB` 与 `mathlean.ini` 不再写死本机路径；相对路径按工程根解析。
- README 里的测试数从 58/75 统一到实际值。

## 1.0.0 — 2026-11-13

从"一堆脚本"重构成可安装、可测试、可自检的工具。

**新增**

- `mathlean` 命令行：`new` / `check` / `status` / `doctor` / `selfcheck` / `upgrade` / `version`。
- 五道门（原来四道）：新增 `docs`，`axioms` 门现在真的检查白名单而不是只 grep `sorryAx`。
- 台账检查新增：依赖图**成环检测**、自定义 `axiom` 登记检查、逐条公理白名单检查。
- 新增台账状态 `CITED`（引自他人、本文未证），必须写明「引用：……」。
- `mathlean ledger --file ... [--tex paper.tex]`：不需要 Lean 工程即可审论文台账，
  `--tex` 会把论文里每个带 `\label` 的定理环境与台账对照（定理类缺失=错误，remark=警告）。
- `mathlean selfcheck`：11 个"故意弄坏"的场景，验证每道门确实会响。
- 69 个单元测试（`python3 -I run_tests.py`）。
- `mathlean doctor`：环境体检，每个失败给出修法。
- 工程自带 `tools/`（vendoring），不依赖本仓库是否存在；`mathlean upgrade` 显式升级。
- `mathlean.ini` 配置：库名、Mathlib 路径、公理白名单、超时、严格模式。
- `docs/ARCHITECTURE.md`、`docs/TROUBLESHOOTING.md`。

**修正**

- `docs` 门不再把脚手架模板当成阶段产物：模板首行带 `<!-- mathlean:template -->` 标记，
  含标记的文件算「未填写」；`mathlean status` 也会标出「模板，未填写」。
  （起因：整条工作流 P5 之后全崩，`check.sh` 仍然报 `OK`，因为 SPEC/CLAIMS/AUDIT 是脚手架复制的。）
- 工作流 Lean 阶段：成功判据从「返回文本以 OK 开头」改成结构化 `{status, detail}`。
  实测中一个 agent 写了"已经存在、编译通过、验证如下……"，被误判为 FAIL，导致
  下游 11 条引理全部阻塞。
- 工作流 Lean 阶段：依赖死锁现在整体点名（谁被谁卡住）并停止，不再"随便挑三条反复重试"
  （那次 139 个 agent 里有一大半是这么空转出来的）。
- `mathlean new --force` 之前根本不能用：骨架里的 `__LIB__/` 改名成已存在的 `Lib/` 会抛
  `OSError: Directory not empty`。现在改成合并；`--force` 只覆盖还没填的模板，
  已写过的阶段产物不动。
- 扫描器支持嵌套块注释、字符串字面量，并保留行号。
- `PROVED` 行在 `Audit.lean` 存在但为空时也会失败（旧版会静默跳过）。
- 台账为空从"错误"改为"跳过"（新工程不该一建好就是红的），`--strict-docs` 下仍为错误。

**移除**

- `scripts/claims_lint.py`、`scripts/scan_sorry.py`：功能并入 `mathlean/`。
  `scripts/new_project.sh` 保留为薄封装。

## 0.9 — 2026-11-13

- 初版骨架：`new_project.sh`、`claims_lint.py`、`scan_sorry.py`、`check.sh`、
  SPEC/CLAIMS/AUDIT 模板、`workflow.js`（P0–P9 编排）、`WORKFLOW.md`。
