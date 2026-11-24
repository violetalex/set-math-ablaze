# mathlean

数学命题求解 + Lean 4 机器验证的工作流工具。

核心主张只有一句：**「我证明了 X」这句话，在每一个环节都被独立检查一次**，
到最后读者能分清哪一条被机器验证过、哪一条只是人类论证、哪一条是条件性的、哪一条还开着。

```
$ mathlean check
mathlean 1.0.0   ~/my-problem   (库 MyProblem)

✔ build    5.96s  lake build 通过
✔ sorry    0.00s  扫描 2 个文件，无 sorry/admit
✔ axioms   5.90s  1 个声明，公理 ⊆ {Classical.choice, Quot.sound, propext}
✔ ledger   0.00s  1 条台账（PROVED 1），0 个错误，0 个警告
✔ docs     0.00s  阶段产物齐全

OK
```

## 两条设计原则

**一、确定性的事情用代码做，需要判断的事情用 agent 做。**

| | 谁做 | 有没有测试 |
|---|---|---|
| 脚手架、编译、扫 sorry、公理审计、台账一致性 | `mathlean`（Python，无第三方依赖） | 有，123 个单元测试 + 13 个自检场景 |
| 证明、找反例、对抗审计、形式化、陈述保真 | `workflow.js` 编排的 agent | 靠 P0–P9 的结构与门禁约束 |

确定性部分出错是**可复现的 bug**；agent 部分出错是**判断失误**。两者要用完全不同的办法兜。
把前者写进代码，才能把注意力留给后者。

**二、每个工程自带一份检查器。**

`mathlean new` 会把 `tools/mathlean/` 复制进工程。好处是工程不依赖本仓库、结果可复现；
代价是升级要显式做：

```sh
mathlean upgrade --root ~/my-problem   # 1.0.0 → 1.1.0
```

## 安装

不需要 pip。仓库自带启动器：

```sh
ln -s ~/math-lean/bin/mathlean ~/.local/bin/mathlean   # 或者直接把 ~/math-lean/bin 加进 PATH
mathlean version
```

也可以用 `pipx install ~/math-lean`（有 `pyproject.toml`）。

## 五分钟上手

```sh
mathlean new ~/my-problem MyProblem     # 建工程（复用已编好的 Mathlib）
cd ~/my-problem

$EDITOR docs/SPEC.md                    # 对象、假设、结论、可伪性（P0）
$EDITOR docs/CLAIMS.md                  # 命题台账（P8）
$EDITOR MyProblem/Basic.lean            # 证明（P6）
$EDITOR Audit.lean                      # 每条定理 #print axioms

bash scripts/check.sh                   # 验收
```

`check.sh` 就是 `mathlean check` 的薄封装，工程里的 `tools/` 自带实现。

## 六道门

| 门 | 检查什么 | 失败意味着 |
|---|---|---|
| `build` | `lake build` | 代码编译不过 |
| `sorry` | 源码里没有 `sorry`/`admit`/`native_decide`/`implemented_by`/`extern`（注释和字符串不算） | 有洞，或有信任 kernel 之外的构造 |
| `axioms` | `Audit.lean` 跑通；每个声明依赖的公理 ⊆ 白名单；自定义 `axiom` 已登记 | 证了，但可能是假证 |
| `statement` | 声明的类型与 `Statements.lean` 里独立重写的 `Challenge.<名字>` 定义等价 | **证的不是那句话** |
| `ledger` | 台账与源码、审计、依赖图一致；依赖不成环 | 陈诉与代码对不上，或循环论证 |
| `docs` | 阶段产物齐全（`--strict-docs` 时强制） | 流程没走完 |

任何一道失败，退出码 1。

`statement` 门是唯一**不读证明**的门。在工程根放一个 `Statements.lean`，由不参与
证明的人把每个 `PROVED` 命题按原样重写一遍：

```lean
namespace Challenge
def Liouville.PhiExt_bound : Prop := ∀ (Γ : ℝ → ℝ → ℝ → ℝ) ..., ...
end Challenge
```

门禁追加 `example : Challenge.Liouville.PhiExt_bound := Liouville.PhiExt_bound`，
由 elaborator 判定两边类型是否定义等价。证明怎么改写都行，类型不对就不过。
没有 `Statements.lean` 时这道门跳过（显示 `·`），不算失败。

它挡不住的是**定义被改**：如果工程里的 `R` 不是论文的 `R`，两边会一起变，
比对仍然通过。那一层靠 `frontier` 的「定义与实例」一节人工核对。

`ledger` 门具体检查：

- 状态只能是 `PROVED` / `PROVED-INFORMAL` / `CONDITIONAL` / `OPEN` / `REFUTED` / `INFORMAL-ONLY` / `CITED`；
- `PROVED` 的 Lean 声明必须真实存在，且在 `Audit.lean` 里有 `#print axioms`；
- `PROVED` 声明的公理集合必须 ⊆ 白名单（默认 `propext`、`Classical.choice`、`Quot.sound`）；
- `CONDITIONAL` 必须写「假设：……」，`REFUTED` 必须写「反例：……」，`CITED` 必须写「引用：……」；
- 依赖列引用的 ID 必须存在，且**依赖图不能有环**（循环论证是头号嫌疑）；
- 表头有「理解」列时，`PROVED` 行必须写 `yes` / `partial` / `no`，
  写 `no` 或 `partial` 的备注里必须写明解读写在哪里。

「理解」这一列回答的是另一件事：**机器证明了，有没有人读懂。** Alpöge 的黎曼猜想证明
就是这个极端情形——kernel 接受、作者本人公开承认还没掌握它。台账里写 `no` 不是认输，
是把"下一步该写什么"标出来；`ledger` 门的输出会带上 `理解 yes 2 / no 0` 这样的计数。

论文不进 Lean 也能查：`mathlean ledger --file CLAIMS.md --tex paper.tex` 不需要 Lean 工程，
却会把 `paper.tex` 里每个带 `\label` 的定理/命题/引理/推论/假设拿去和台账对照——
定理类没被引用是错误，remark 没被引用是警告，没有 `\label` 的只计数。

## 审计面（`frontier`）

六道门回答「证得对不对」，但没有回答：**证明本体之外，还有哪些事实在被使用？**

```
mathlean frontier                 # 从台账的 PROVED 行出发
mathlean frontier --target Foo.x  # 指定声明
mathlean frontier --write docs/FRONTIER.md
```

做法：沿**项目内部**的声明做传递闭包（在 Mathlib 边界停下，不展开），收集闭包里
每个声明直接引用的外部常量，按来源分成五类：

| 类别 | 含义 | 要不要人看 |
|---|---|---|
| 公理 | `axiom` / `sorryAx` | 永远要 |
| 数学定理 | 工程外的非策略命题 | **要，这就是审计面** |
| 策略支撑 | `Mathlib.Tactic.*`，`ring`/`field_simp` 展开的引理 | 不用逐条 |
| 定义与实例 | 定义、结构、实例投影 | 不用逐条，但定义被改过定理就换了意思 |
| 语言基础 | `Init` / `Lean` / `Std` / `Batteries` | 不用 |

证明越长大，这个分类越重要：中段交给 kernel，两端留给人。
参考 `formalization/docs/FRONTIER.md`——两个定理、437 条外部引用，
其中真正需要核对的是 95 条数学定理。

## 命令

```
mathlean new <目录> <库名>      建工程
mathlean check                  验收（--no-build / --no-audit / --json）
mathlean ledger --file C.md     只查台账（--tex 顺带核对论文环境覆盖）
mathlean frontier               算审计面：证明从工程外借用了什么（--write 写 markdown）
mathlean replay                 把编译产物交给 kernel 重放（不经 elaborator）
mathlean search                 在引理 DAG 上排下一轮该攻哪里（--policy rr|greedy|ucb）
mathlean status                 看工程现状：阶段产物、台账计数、运行记录
mathlean doctor                 环境体检：elan、lake、Mathlib、配置
mathlean selfcheck              验证门禁本身按预期工作（13 个场景）
mathlean upgrade                更新工程里的 tools/
mathlean version
```

## kernel 重放（`replay`）

`build` 门信任的是 elaborator：它展开宏、跑 tactic、允许 `addDecl` 这类逃逸口。
真正决定证明成立的是 kernel，而 `lake build` 通过并不等于 kernel 接受。
`mathlean replay` 用 `leanchecker` 读 `.olean`，把每个模块重新交给 kernel 检查：

```
$ mathlean replay
Lean      Lean (version 4.34.1, ...)
Mathlib   d13f23b723b8
检查器    leanchecker
✔ Liouville                         24.81s
```

`leanchecker` 会顺着 import 图把依赖一起检查，所以只跑入口模块就够。

**边界**：`leanchecker` 是 Lean 自带的，与本工程共用同一个 kernel 实现。
它防的是"elaborator 环节被绕过"，防不了"kernel 本身有 bug"。真正独立的实现
（nanoda）需要单独安装，`--checker` 参数留了这个口子。

## 调度（`search`）

"下一轮该攻哪条引理"现在是个显式的、可复现的选择：

```
$ mathlean search --write
策略 greedy   就绪 11   未就绪 19   终态 5   已死 0
   1. A9     分数   2.81  被引用 3  陈述 46 字  试过 0 次  [PROVED-INFORMAL]
   2. A8     分数   1.53  被引用 2  陈述 113 字 试过 0 次  [PROVED-INFORMAL]
```

- **就绪** = 状态还可推进（`OPEN` / `CONDITIONAL` / `PROVED-INFORMAL` / `INFORMAL-ONLY`）
  且依赖都是 `PROVED` 或 `CITED`；依赖里有 `REFUTED` 的记为**已死**。
- **打分** = `被引用次数 − 0.5×(陈述字数/120) − 0.3×已试次数`。
- **策略**：`rr` 按 ID 轮转（基线）、`greedy` 按分数、`ucb` 用上一轮日志推断出的奖励。
- `--write` 把本轮决策连同当时的全部状态写进 `docs/RUNS/search-<时间>.json`。

**为什么要落盘。** 下一轮读回上一轮的 `picks` 和 `statuses`，就能算出"上次挑的那些有没有前进"，
这就是奖励。有了日志，策略才可离线对比——先有记录，再谈优化。

**边界**：动作空间里没有"改陈述"。陈述由 `Statements.lean` 钉死；调度器只决定顺序，
不决定证什么。否则最优策略一定是把定理证成平凡的。

## 跟着 Claude Code 跑

最省事的入口是斜杠命令：

```
/math-lean 设 u 是轴对称 NS 的古代解且 b^ρ ≥ 0，证明 Γ ≡ 0
```

它建工程、写 SPEC、调 `workflow.js` 跑 P0–P9、最后跑 `check.sh`。
编排细节见 [WORKFLOW.md](WORKFLOW.md)。

## 仓库结构

```
bin/mathlean          启动器（python3 -I，不污染 sys.path）
mathlean/             检查器本体
  config.py             读取 mathlean.ini
  lean_scan.py          注释剥离、sorry 扫描、声明抽取（含 namespace）
  audit.py              跑 lake env lean，解析 #print axioms 输出
  ledger.py             台账解析、行内规则、依赖环检测
  paper.py              LaTeX 定理环境 ↔ 台账 覆盖核对
  checks.py             六道门
  scaffold.py           建工程 / vendoring
  doctor.py             环境体检
  selfcheck.py          门禁自检
tests/                123 个单元测试：python3 -I run_tests.py
workflow.js           P0–P9 多 agent 编排
WORKFLOW.md           方法论：十条铁律、阶段、门禁
docs/ARCHITECTURE.md  为什么这样分层
docs/TROUBLESHOOTING.md 常见故障
templates/            SPEC / CLAIMS / AUDIT 模板
lean/                 Lean 骨架
```

## 关键约定

- **状态只有六种**，台账是唯一真相；论文措辞由台账决定，不由记忆决定。
- **Lean 里不允许 `sorry`**；写不动就退回证明阶段，而不是留洞。
- **允许公理**：`propext`、`Classical.choice`、`Quot.sound`。自定义 `axiom` 必须登记。
- **工具输出不可信**：所以本工具自己也有 `selfcheck`。
- **没证出来的就写没证出来**，`OPEN` 和 `REFUTED` 也是成果。
