# 命题台账：CNN 完备解释

> 唯一真相。论文里每一句"我们证明了……"都必须能追到这里的某一行。
> 规范见 `docs/SPEC.md`（P0 已锁定）。

## 状态取值

| 状态 | 含义 | 额外要求 |
|---|---|---|
| `PROVED` | Lean 4 机器验证通过 | 「Lean 声明」列是真实声明名，且 `Audit.lean` 里有 `#print axioms` |
| `PROVED-INFORMAL` | 只有人类证明 | 备注写"未形式化"及原因 |
| `CONDITIONAL` | 在若干假设下成立 | 备注必须写「假设：……」 |
| `OPEN` | 没有证明，也没有反例 | 备注写卡在哪里 |
| `REFUTED` | 有反例 | 备注必须写「反例：……」 |
| `INFORMAL-ONLY` | 依赖 Mathlib 缺失的工具 | 备注写缺什么 |

## 台账

| ID | 状态 | 命题 | Lean 声明 | 依赖 | 理解 | 备注 |
|---|---|---|---|---|---|---|
| C1 | PROVED | 仿射映射的复合仍是仿射，且线性部分 = 矩阵乘积、常数项 = `A b' + b` | `CnnExplain.Affine.comp_apply` | — | yes | 机器验证；只用了 `Matrix.mulVec_add`、`Matrix.mulVec_mulVec` 与 `abel` |
| C2 | PROVED | 单层仿射网络等于该仿射映射本身 | `CnnExplain.net_affine_apply` | C1 | yes | 归纳的基例。注意：本条证的是 **eval 侧**（`Net.apply [affine f] = f.apply`），`linOf` 侧的同一事实由 `walk` 的定义展开可得，未单列（审计 PLAUSIBLE） |
| C3 | PROVED | 单层 ReLU 网络：模式分两支，`linOf` 在开分支是恒等、关分支是零 | `CnnExplain.ReLU.apply_eq_linear` | — | yes | 基例；辅助引理 `ReLU.linear_apply` 把对角矩阵乘向量化成逐点式 |
| C4 | PROVED | 归纳步：两个输入的模式序列相同，则 `eval net y = (linOf net x).apply y` | `CnnExplain.eval_eq_lin` | C1, C2, C3 | yes | 前向递归 `walk` + 对层表归纳；仿射层用 `comp_apply`，ReLU 层用 C3 把 `linear` 换回 `apply` |
| C5 | PROVED | **主定理**：∀ net ∀ x ∃ σ, x ∈ region σ ∧ ∀ y ∈ region σ, eval net y = linOf σ y | `CnnExplain.exists_explanation` | C4 | yes | σ := `patternOf net x`，存在性是构造的 |
| C6 | PROVED | 推论：∀ x, eval net x = linOf (patternOf net x) x（预测由激活模式决定） | `CnnExplain.eval_self` | C5 | yes | 取 y = x，区域条件 `rfl` |
| C7 | PROVED | 边界相容：前激活值 = 0 时归入关分支，两分支的值相同 | `CnnExplain.ReLU.boundary_agrees` | C3 | yes | `x i ≤ 0` 时模式判 false；`max_eq_right` 给出 0，与关分支一致 |
| C8 | PROVED | 卷积与循环平移可交换（Toeplitz 结构的数学内容） | `CnnExplain.Conv.convOp_shift` | — | yes | `convOp k x i = ∑ m, k m * x (i+m)` 实为**互相关**，等同于翻转核的卷积（`k` 遍历整个向量），故等变性与完备性不受影响——**论文措辞须写 cross-correlation** |
| C9 | PROVED | 最大池化的值等于窗口内某个坐标的值（池化 = 选择；并列时选哪个不影响值） | `CnnExplain.Pool.is_selection` | — | yes | `Classical.choose` 给出确定的选择，`choice_eq` 说明它取到最大 |
| C10 | PROVED | CNN 的完备解释定理（C5 在 C8/C9 上的实例化） | `CnnExplain.cnn_explanation` | C5, C8, C9 | yes | 具名的实例只固化了 `[conv, relu, pool]` 三层；**任意多层**的情形由 C5 直接给出 | `Layer` 增加池化构造子，`Pattern` 改为 `Pat` 列表（记录 ReLU 开关与池化选择），`walk`/`eval_eq_lin` 扩到三种情况；CNN 写成 `Net` 后由 C5 直接给出 |
| C11 | PROVED | **二维** CNN 的完备解释定理（索引取 `Fin h × Fin w`） | `CnnExplain.cnn2d_explanation` | C10 | yes | 索引类型从 `Fin n` 抽象成任意有限加法交换半群，二维是 `Grid h w := Fin h × Fin w` 的实例——**没有第二套证明** |
| C12 | PROVED | 二维卷积与二维循环平移可交换 | `CnnExplain.conv2d_shift` | C8 | yes | C8 在 `Grid h w` 上的特化 |
| C19 | PROVED | 仿射映射的球上延拓唯一性：两个仿射映射在半径 r>0 的球上处处相等 ⇒ 相等 | `CnnExplain.Unique.affine_ext_on_ball` | — | yes | 标准引理；在球心比常数项，在球心加 `(r/2)·e_k` 比第 k 列 |
| C20 | PROVED | **解释的唯一性**：`Bounds` 成立且 R>0 时，任何在球上与网络相等的仿射映射都等于 `linOf net x` | `CnnExplain.Unique.explanation_unique` | C4, C17, C19 | yes | 把"存在一个解释"升级为"这个解释被唯一决定"；由 C17 给出球在区域内，再由 C19 得唯一 |
| C18 | PROVED | **感受野**：线性化矩阵的每个非零元都落在 `rowSupport net x i` 内（递归定义的依赖集合） | `CnnExplain.Field.mem_rowSupport` | — | yes | 补上审计指出被删掉的那条"按感受野分解"：矩阵的零模式由结构决定，与输入无关 |
| C14 | PROVED | ReLU 的局部符号稳定：x 的坐标离 0 严格大于 ε、y 与 x 之差不超过 ε ⇒ 两者 ReLU 模式相同 | `CnnExplain.Local.relu_pattern_stable` | — | yes | 半径估计的第一块地基；`Close` 用非严格 `≤`，所以 margin 必须严格 |
| C15 | PROVED | 池化的局部选择稳定：窗口最大值严格高出 δ、y 与 x 之差不超过 δ/2 ⇒ 选中的坐标不变 | `CnnExplain.Local.pool_choice_stable` | — | yes | 需要严格最大值，否则 `Classical.choose` 的平局选择会随输入漂移 |
| C16 | PROVED | **局部半径**：`0 < R` 且每层 margin / gap 满足 `Bounds` ⇒ 半径 R 内扰动不改变模式序列 | `CnnExplain.Local.stable_of_bounds` | C14, C15 | yes | 仿射层按 `max (rowSup A) 1` 放大半径（保守）；这是让"解释能用多远"成为定理的那一步 |
| C17 | PROVED | 完备解释的**局部版本**：半径 R 内的点都落在同一模式区域，C5 的线性化在那个球上处处有效 | `CnnExplain.Local.local_region` | C16 | yes | C5 的几何化补充；不再只说"区域上成立"，而说"球上成立" |
| C13 | PROVED | 零填充**破坏**平移等变，且给出显式反例（`n=3`、核取偏移 1、输入 `[1,2,3]`） | `CnnExplain.ZeroPad.breaks_shift` | C8 | yes | 这是**否定结果**，不是缺陷：循环卷积的等变性无条件，零填充把边界代价显式化。反例在坐标 1 处差 `1 ≠ 0` |

## 第一阶段范围（C1–C7）

只涉及 `Mat` / `Vec` / `max` / `Finset`，全部可由 Mathlib 直接支撑。
卷积与池化不在其中——它们是"结构化仿射"，第二阶段才引入。

## 第二阶段范围（C8–C10）

把 CNN 变成 C5 的实例，而不是另起一套理论。

**一处不能再说的**：这里原本写着"解释按感受野分解"是本工程区别于全连接文献之处。
审计指出——**代码里没有这条定理**：`cnn_explanation` 只是把 CNN 塞进 C5，
`linOf` 仍是整条网络的稠密仿射映射，没有任何稀疏性或 Toeplitz 结构被证明。
把 `M` 的卷积结构写成定理是未做的工作（见 `docs/AUDIT.md` §3）。

## 与论文的对应

| 论文位置 | 台账 ID |
|---|---|
| （待写：完备解释定理） | C5, C6 |
| （待写：为什么不需要紧凑性） | 无（SPEC §5 的范围声明） |

## 变更记录

- 2026-11-27：建表。SPEC 锁定，全部条目 `OPEN`，未写 Lean。
