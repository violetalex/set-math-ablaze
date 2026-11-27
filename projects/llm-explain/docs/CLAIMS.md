# 命题台账

> 唯一真相。论文里每一句"我们证明了……"都必须能追到这里的某一行。
> 由 `mathlean check` 的 `ledger` 门自动检查（工程里是 `bash scripts/check.sh`）。

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

<!-- 七列，缺一列检查脚本会跳过该行；ID 用 C1、C2… -->

| ID | 状态 | 命题 | Lean 声明 | 依赖 | 理解 | 备注 |
|---|---|---|---|---|---|---|
| C1 | PROVED | softmax 的分母严格为正 | `LlmExplain.exp_sum_pos` | — | yes | `exp > 0` 加 `I` 非空 |
| C2 | PROVED | softmax 的每个分量严格为正 | `LlmExplain.softmax_pos` | C1 | yes | 正数除正数 |
| C3 | PROVED | softmax 的分量之和为 1 | `LlmExplain.softmax_sum` | C1 | yes | 求和与除法交换，再 `div_self` |
| C4 | PROVED | 注意力输出落在值的范围内（凸组合） | `LlmExplain.attn_range` | C2, C3 | yes | 三角不等式 + 非负加权 + 权重和为 1 |
| C5 | PROVED | softmax 只依赖分差（整体平移不变） | `LlmExplain.softmax_shift` | — | yes | `exp(z+c)=exp z·exp c`，约掉 |
| C6 | PROVED | softmax 对分差单调 | `LlmExplain.softmax_mono` | C1 | yes | `exp_le_exp` + 同分母 |
| C7 | PROVED | gap 控制 top-1 权重：严格最大且次大低 δ ⇒ `p* ≥ 1/(1+(\|I\|-1)e^{-δ})` | `LlmExplain.Gap.softmax_ge_of_gap` | C3 | yes | 把 softmax 写成相对分差的指数和的倒数，再逐项估界 |
| C8 | PROVED | 注意力输出与任一 `v i₀` 之差 ≤ `(1-p_{i₀})·2M` | `LlmExplain.Gap.hard_attn_error` | C3, C4 | yes | **对任意 `i₀` 无条件成立**（不需要 gap，也不需要 `i₀` 是 argmax）。"gap 让逼近变好"要靠 C7 与 C8 合用，但**这条合并陈述没有单列**；`2M` 是紧的（换成 `M` 会被 `Fin 2` 的反例推翻） |
| C26 | PROVED | **模糊度的维数**：与给定输出相容的权重组，至少含 `\|I\| − (\|D\| + 1)` 维仿射子空间 | `LlmExplain.ker_finrank_ge` | C25 | yes | 秩-零化度。`n=2048, d=768` 时是 **1279 维**的模糊——不是"另有一个解"，是"一整族解" |
| C27 | PROVED | 往权重上加核里的任何向量，**输出与权重和都不变** | `LlmExplain.fiber_contains` | C26 | yes | 把 C26 的维数变成实际的模糊：沿整个核方向都是解 |
| C25 | PROVED | **长序列不可逆**：仿射无关 ⇒ `\|I\| ≤ \|D\| + 1` | `LlmExplain.card_le_of_affinelyIndependent` | — | yes | 线性映射 `c ↦ (∑ c_i v_i, ∑ c_i)` 单射 ⇒ 维数比较。**推论**：`\|I\| > \|D\| + 1` 时（真实 transformer 的常态）值向量必然仿射相关，由 C23 **注意力权重不可从输出恢复** |
| C28 | PROVED | **C23 的逆**：仿射相关时存在两个**不同的概率向量**给出相同输出 | `LlmExplain.exists_second_explanation` | C23 | yes | 从均匀权出发沿非零零组合走一小步 `ε`，保持非负与和为 1。与 C23 合起来使"当且仅当"成为**双向机器验证** |
| C23 | PROVED | **注意力的可逆性**：值向量仿射无关时，`attn p v = attn p′ v` 与 `∑p = ∑p′ = 1` 蕴含 `p = p′` | `LlmExplain.attn_injective` | — | yes | 反问题：**输出唯一确定权重**。只是单射不是满射。P1：检索 `attention+identifiab` / `attention+invertib` 均 0 命中；最近的 `arXiv:2310.12462` 是**反方向**（权重→数据）。数学是标准线性代数，价值在问法，只能写 "to our knowledge" |
| C24 | PROVED | **C5 的逆**：`softmax z = softmax z′ ⇒ ∃ c, z′ = z + c` | `LlmExplain.softmax_eq_iff_shift` | C1 | yes | 与 C5 合起来：softmax 把分数**精确地**商掉一个平移自由度。C23 + C24 构成完整的可逆性链：输出 → 权重 → 分数（模常数） |
| C22 | PROVED | **注意力严格收缩**：权重每项 ≥ m、每行和为 1 ⇒ `\|out i − out j\| ≤ (1 − \|I\|·m) · D`（D 为值跨度） | `LlmExplain.attention_contracts` | C2, C3 | yes | 唯一一条**动力学**结论：softmax 权重严格为正（C2）⇒ m>0 ⇒ 因子 < 1，**无条件收缩**。均匀权重时因子为 0（立刻 rank 1），集中权重时因子趋 1（不收缩）——界在两端的插值都对。**非新结果**：rank collapse 见 Dong et al., `arXiv:2103.03404`；本工程是它的机器验证版与显式常数版 |
| C20 | PROVED | **深度塌缩**：两个线性注意力层 `X ↦ P·X·W` 的复合仍是同一形状，参数为 `(P₂P₁, W₁W₂)` | `LlmExplain.linLayer_comp` | — | yes | 归结为矩阵结合律；归纳下去任意深度塌缩成一层 |
| C21 | PROVED | **残差产生交叉项**：`(1+A)(1+B) = 1 + A + B + A·B` | `LlmExplain.residual_cross_term` | — | yes | `A·B` 是单层拿不到、只有深度才产生的项——这是"为什么需要残差"的代数回答 |
| C16 | PROVED | **平移不变性迫使乘性 Cauchy 方程**：逐点权重 `f a/(f a+f b)` 平移不变 ⇒ `f(a+c)·f b = f a·f(b+c)` | `LlmExplain.shift_inv_forces_multiplicative` | — | yes | "为什么是 softmax"的核心一步：不是任意函数都能当权重生成器 |
| C17 | PROVED | 指数族满足平移不变性：任意温度 `lam` 的 softmax 都是解 | `LlmExplain.exp_weight_shift_invariant` | — | yes | C16 的逆方向的一半 |
| C18 | OPEN | **深度层级猜想**：对每个 L，存在一个函数，L+1 层注意力可算，而任何 L 层、多项式宽度的注意力网络都不能 | — | — | — | **记录为 OPEN，不作为论文主张。** 这类陈述蕴含电路深度—规模下界，属于当前数学无法触及的范围；本工程不声称能证 |
| C19 | INFORMAL-ONLY | 乘性 Cauchy 方程 `g(a+c)=g a·g c` 在**正、连续**条件下的解必为指数 | — | — | — | 缺这一环，未形式化。**没有正则性时命题为假**：该方程有大量 Hamel 基构造的病态解；且 `g ≡ 0` 也是解（故需 `f > 0`，见 SPEC (H3)）。即使补上，也只到"温度自由"的指数族，不是 $\lambda=1$ 的 softmax；且本工程只做了两位置 |
| C14 | PROVED | 注意力输出对值 1-Lipschitz：`\|attn v − attn v′\| ≤ M` | `LlmExplain.attn_value_lipschitz` | C2, C3 | yes | 只用权重非负且和为 1；与权重具体取值无关 |
| C15 | PROVED | 单个残差块对（残差, 值）的联合界：`≤ \|x−x′\| + M`（分数固定） | `LlmExplain.block_lipschitz` | C14 | yes | 单块的界。**跨层复合没有形式化**，所以"深度增加时线性增长"这句话目前**没有定理支撑** |
| C12 | PROVED | softmax 作为 `z` 的映射是单调算子：`⟨p − p′, z − z′⟩ ≥ 0` | `LlmExplain.softmax_monotone` | — | yes | 右边等于 `KL(p‖p′) + KL(p′‖p)`，由 Gibbs（辅助引理 `kl_nonneg`）非负。**范围**：这是关于 `z ↦ softmax z` 的陈述；transformer 里 `z` 由权重与输入决定，**复合映射不受此约束**。"等价于 logsumexp 的梯度"是正确数学但**未形式化**（`logsumexp` 未定义） |
| C13 | PROVED | 加权方差非负：`(∑ p i a i)² ≤ ∑ p i (a i)²` | `LlmExplain.softmax_variance_nonneg` | — | yes | Cauchy–Schwarz（开方形式）。**只有这条标量不等式被证明**；"雅可比对称半正定、行和为零、秩 ≤ \|I\|−1"是未形式化的推论 |
| C10 | PROVED | 残差块的输出范围：`\|block z v x d\| ≤ A + B` | `LlmExplain.block_range` | C4 | yes | 三角不等式 + C4；把"一个头"抬到"一层" |
| C11 | PROVED | 残差块与「残差 + 单个值」之差 ≤ `(1-p*)·2M` | `LlmExplain.block_close_to_hard` | C8 | yes | C8 的层级别版本。**注意**：对一个**固定**的 `i₀`，右边 `x d + v i₀ d` 对 `x` 是仿射的；把它说成"分段线性代理"需要先定义 argmax 选择，本工程**没有定义** |
| C9 | PROVED | `rms` 是一次齐次的：`rms (c · x) = \|c\| · rms x` | `LlmExplain.rms_smul` | — | yes | **修正过**：SPEC 初稿写的「rmsnorm 对缩放不变」在 ε>0 时是假的，已改为真正的齐性陈述 |

「理解」列：`yes` / `partial` / `no`，`PROVED` 行必填。
机器证明了不等于有人读懂——`no` 表示 kernel 接受了、但还没人讲清它为什么成立，
此时备注必须写明解读写在哪里。其它状态可以留 `—`。

## 写法示例

```
| C1 | PROVED | 若 b^ρ ≥ 0 则 Γ ≡ 0 | IsEven.add | — | yes | 论文定理 1.1 |
| C2 | CONDITIONAL | 逃逸平台处 Γ ≡ 0 | — | C1 | — | 假设：ρ ≳ (−t)^{1/4} 且 |Γ| ≥ L/2 |
| C4 | REFUTED | V = −4νρ/(1+ρ²) 是反例 | — | — | — | 反例：加权无散条件失效 |
```

- 「Lean 声明」填源码里 `theorem`/`lemma` 后面的名字（`IsEven.add` 或全名 `Lib.IsEven.add` 均可）。
- 填了 `PROVED` 却没在 `Audit.lean` 里 `#print axioms`，检查脚本会报错——这正是要防的。

## 与论文的对应

`paper/main.tex` 里每个定理类环境的 `\label` 与台账行的对应。`mathlean ledger --tex`
按这张表核对（label 必须出现在台账文本里）。

| 论文环境 | 台账 |
|---|---|
| `def:affind` | C23（仿射无关的定义，`LlmExplain.AffinelyIndependent`） |
| `thm:inj` | C23 |
| `thm:conv` | C28 |
| `prop:shift` | C5, C24 |
| `thm:dim` | C25 |
| `thm:kerdim` | C26 |
| `cor:fiber` | C27 |
| `prop:prob` | C1, C2, C3 |
| `prop:conv` | C4 |
| `prop:diff` | C5, C6 |
| `prop:gap` | C7, C8 |
| `thm:contract` | C22 |
| `prop:depth` | C20, C21 |

论文**没有**逐条重述的台账：C9（`rms` 齐性）、C10–C11（残差块）、C12–C13（单调与方差）、
C14–C15（值路径）、C16–C17（两位置刻画）、C18（OPEN）、C19（INFORMAL-ONLY）。
它们只出现在附录表里。

## 变更记录

- YYYY-MM-DD：C2 由 PROVED 降级为 CONDITIONAL，原因 ……
- YYYY-MM-DD：C4 撤回原证明，改为反例 ……
