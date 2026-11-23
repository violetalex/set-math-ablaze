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
| 脚手架、编译、扫 sorry、公理审计、台账一致性 | `mathlean`（Python，无第三方依赖） | 有，86 个单元测试 + 12 个自检场景 |
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

## 五道门

| 门 | 检查什么 | 失败意味着 |
|---|---|---|
| `build` | `lake build` | 代码编译不过 |
| `sorry` | 源码里没有 `sorry`/`admit`（注释和字符串不算） | 有没补完的证明 |
| `axioms` | `Audit.lean` 跑通；每个声明依赖的公理 ⊆ 白名单；自定义 `axiom` 已登记 | 证了，但可能是假证 |
| `ledger` | 台账与源码、审计、依赖图一致；依赖不成环 | 陈诉与代码对不上，或循环论证 |
| `docs` | 阶段产物齐全（`--strict-docs` 时强制） | 流程没走完 |

任何一道失败，退出码 1。

`ledger` 门具体检查：

- 状态只能是 `PROVED` / `PROVED-INFORMAL` / `CONDITIONAL` / `OPEN` / `REFUTED` / `INFORMAL-ONLY` / `CITED`；
- `PROVED` 的 Lean 声明必须真实存在，且在 `Audit.lean` 里有 `#print axioms`；
- `PROVED` 声明的公理集合必须 ⊆ 白名单（默认 `propext`、`Classical.choice`、`Quot.sound`）；
- `CONDITIONAL` 必须写「假设：……」，`REFUTED` 必须写「反例：……」，`CITED` 必须写「引用：……」；
- 依赖列引用的 ID 必须存在，且**依赖图不能有环**（循环论证是头号嫌疑）。

论文不进 Lean 也能查：`mathlean ledger --file CLAIMS.md --tex paper.tex` 不需要 Lean 工程，
却会把 `paper.tex` 里每个带 `\label` 的定理/命题/引理/推论/假设拿去和台账对照——
定理类没被引用是错误，remark 没被引用是警告，没有 `\label` 的只计数。

## 审计面（`frontier`）

五道门回答「证得对不对」，但没有回答：**证明本体之外，还有哪些事实在被使用？**

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
mathlean status                 看工程现状：阶段产物、台账计数、运行记录
mathlean doctor                 环境体检：elan、lake、Mathlib、配置
mathlean selfcheck              验证门禁本身按预期工作（12 个场景）
mathlean upgrade                更新工程里的 tools/
mathlean version
```

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
  checks.py             五道门
  scaffold.py           建工程 / vendoring
  doctor.py             环境体检
  selfcheck.py          门禁自检
tests/                86 个单元测试：python3 -I run_tests.py
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
