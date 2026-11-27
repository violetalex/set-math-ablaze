/-
挑战文件：`statement` 门用的独立陈述。

原则：这里写的是"我们声称证了什么"，与 `LlmExplain/Basic.lean` 里的证明无关。
写法上逐字对应 `docs/SPEC.md` 的定义台账。

命名约定：`Challenge.<Lean 声明名>`。

**量词结构必须与声明一致**（含 implicit/explicit 与类型类绑定顺序）。
这是这道门的已知局限：它比数学更严。
-/

import Mathlib
import LlmExplain

namespace Challenge

/-- 台账 C1：softmax 的分母严格为正。 -/
def LlmExplain.exp_sum_pos : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ), 0 < ∑ j, Real.exp (z j)

/-- 台账 C2：softmax 的分量严格为正。 -/
def LlmExplain.softmax_pos : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ) (i : I),
    0 < LlmExplain.softmax z i

/-- 台账 C3：softmax 的分量之和为 1。 -/
def LlmExplain.softmax_sum : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ),
    ∑ i, LlmExplain.softmax z i = 1

/-- 台账 C4：注意力输出落在值的范围内。 -/
def LlmExplain.attn_range : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] {D : Type*}
    (z : I → ℝ) (v : I → D → ℝ) (d : D) {M : ℝ},
    (∀ i, |v i d| ≤ M) → |LlmExplain.attn (LlmExplain.softmax z) v d| ≤ M

/-- 台账 C5：softmax 整体平移不变（只依赖分差）。 -/
def LlmExplain.softmax_shift : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ) (c : ℝ),
    LlmExplain.softmax (fun i => z i + c) = LlmExplain.softmax z

/-- 台账 C6：softmax 对分差单调。 -/
def LlmExplain.softmax_mono : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z : I → ℝ) {i j : I},
    z i ≤ z j → LlmExplain.softmax z i ≤ LlmExplain.softmax z j

/-- 台账 C7：gap 控制 top-1 权重下界。 -/
def LlmExplain.Gap.softmax_ge_of_gap : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (z : I → ℝ) (i₀ : I) {δ : ℝ},
    0 < δ → (∀ j, j ≠ i₀ → z j ≤ z i₀ - δ) →
      1 / (1 + ((Fintype.card I : ℝ) - 1) * Real.exp (-δ))
        ≤ LlmExplain.softmax z i₀

/-- 台账 C8：硬注意力逼近的误差界。 -/
def LlmExplain.Gap.hard_attn_error : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] {D : Type*}
    (z : I → ℝ) (v : I → D → ℝ) (d : D) (i₀ : I) {M : ℝ},
    (∀ i, |v i d| ≤ M) →
      |LlmExplain.attn (LlmExplain.softmax z) v d - v i₀ d|
        ≤ (1 - LlmExplain.softmax z i₀) * (2 * M)

/-- 台账 C9：`rms` 的一次齐性。 -/
def LlmExplain.rms_smul : Prop :=
  ∀ {D : Type*} [Fintype D] (x : D → ℝ) (c : ℝ),
    LlmExplain.rms (fun d => c * x d) = |c| * LlmExplain.rms x

/-- 台账 C10：残差块输出的范围界。 -/
def LlmExplain.block_range : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] {D : Type*}
    (z : I → ℝ) (v : I → D → ℝ) (x : D → ℝ) {A B : ℝ},
    (∀ d, |x d| ≤ A) → (∀ i d, |v i d| ≤ B) → ∀ d,
      |LlmExplain.block z v x d| ≤ A + B

/-- 台账 C11：残差块与其分段线性代理之差。 -/
def LlmExplain.block_close_to_hard : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] {D : Type*}
    (z : I → ℝ) (v : I → D → ℝ) (x : D → ℝ) (d : D) (i₀ : I) {M : ℝ},
    (∀ i, |v i d| ≤ M) →
      |LlmExplain.block z v x d - (x d + v i₀ d)|
        ≤ (1 - LlmExplain.softmax z i₀) * (2 * M)

/-- 台账 C12：注意力头是梯度映射（单调性 / 不能反向选择）。 -/
def LlmExplain.softmax_monotone : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z z' : I → ℝ),
    0 ≤ ∑ i, (LlmExplain.softmax z i - LlmExplain.softmax z' i) * (z i - z' i)

/-- 台账 C13：softmax 的线性响应是协方差（加权方差非负）。 -/
def LlmExplain.softmax_variance_nonneg : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] (z a : I → ℝ),
    (∑ i, LlmExplain.softmax z i * a i) ^ 2 ≤ ∑ i, LlmExplain.softmax z i * a i ^ 2

/-- 台账 C14：注意力输出对值的 Lipschitz 性。 -/
def LlmExplain.attn_value_lipschitz : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] {D : Type*}
    (z : I → ℝ) (v v' : I → D → ℝ) (d : D) {M : ℝ},
    (∀ i, |v i d - v' i d| ≤ M) →
      |LlmExplain.attn (LlmExplain.softmax z) v d
        - LlmExplain.attn (LlmExplain.softmax z) v' d| ≤ M

/-- 台账 C15：残差块的联合 Lipschitz 界。 -/
def LlmExplain.block_lipschitz : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] {D : Type*}
    (z : I → ℝ) (x x' : D → ℝ) (v v' : I → D → ℝ) (d : D) {M : ℝ},
    (∀ i, |v i d - v' i d| ≤ M) →
      |LlmExplain.block z v x d - LlmExplain.block z v' x' d| ≤ |x d - x' d| + M

/-- 台账 C16：平移不变性迫使乘性 Cauchy 方程。 -/
def LlmExplain.shift_inv_forces_multiplicative : Prop :=
  ∀ (f : ℝ → ℝ), (∀ x, 0 < f x) →
    (∀ a b c, LlmExplain.weight2 f (a + c) (b + c) = LlmExplain.weight2 f a b) →
      ∀ a b c, f (a + c) * f b = f a * f (b + c)

/-- 台账 C17：指数族满足平移不变性。 -/
def LlmExplain.exp_weight_shift_invariant : Prop :=
  ∀ (lam : ℝ) (a b c : ℝ),
    LlmExplain.weight2 (fun x => Real.exp (lam * x)) (a + c) (b + c)
      = LlmExplain.weight2 (fun x => Real.exp (lam * x)) a b

/-- 台账 C20：线性注意力层的复合仍是线性注意力层。 -/
def LlmExplain.linLayer_comp : Prop :=
  ∀ {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I] [DecidableEq D]
    (P₂ P₁ : Matrix I I ℝ) (W₁ W₂ : Matrix D D ℝ) (X : Matrix I D ℝ),
    LlmExplain.linLayer P₂ W₂ (LlmExplain.linLayer P₁ W₁ X)
      = LlmExplain.linLayer (P₂ * P₁) (W₁ * W₂) X

/-- 台账 C21：残差连接的交叉项。 -/
def LlmExplain.residual_cross_term : Prop :=
  ∀ {I : Type*} [Fintype I] [DecidableEq I] (A B : Matrix I I ℝ),
    (1 + A) * (1 + B) = 1 + A + B + A * B

/-- 台账 C22：注意力严格收缩 token 之间的差异。 -/
def LlmExplain.attention_contracts : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (p : I → I → ℝ) (m : ℝ),
    (∀ i k, m ≤ p i k) → 0 ≤ m → (∀ i, ∑ k, p i k = 1) →
      ∀ (v : I → ℝ) (c D : ℝ), (∀ k, |v k - c| ≤ D / 2) → ∀ i j,
        |∑ k, p i k * v k - ∑ k, p j k * v k|
          ≤ (1 - (Fintype.card I : ℝ) * m) * D

/-- 台账 C23：仿射无关的值向量使注意力权重可从输出恢复。 -/
def LlmExplain.attn_injective : Prop :=
  ∀ {I D : Type*} [Fintype I] [DecidableEq I] (v : I → D → ℝ),
    LlmExplain.AffinelyIndependent v →
      ∀ {p p' : I → ℝ}, (∑ i, p i = 1) → (∑ i, p' i = 1) →
        LlmExplain.attn p v = LlmExplain.attn p' v → p = p'

/-- 台账 C24：两个 softmax 相同当且仅当分数只差常数。 -/
def LlmExplain.softmax_eq_iff_shift : Prop :=
  ∀ {I : Type*} [Fintype I] [Nonempty I] {z z' : I → ℝ},
    LlmExplain.softmax z = LlmExplain.softmax z' → ∃ c, ∀ i, z' i = z i + c

/-- 台账 C25：仿射无关迫使 `|I| ≤ |D| + 1`（长序列因此不可逆）。 -/
def LlmExplain.card_le_of_affinelyIndependent : Prop :=
  ∀ {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (v : I → D → ℝ),
    LlmExplain.AffinelyIndependent v → Fintype.card I ≤ Fintype.card D + 1

/-- 台账 C26：模糊度的维数。 -/
def LlmExplain.ker_finrank_ge : Prop :=
  ∀ {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (v : I → D → ℝ),
    Fintype.card I - (Fintype.card D + 1)
      ≤ Module.finrank ℝ (LinearMap.ker (LlmExplain.ambMap v))

/-- 台账 C27：核方向不改变输出与权重和。 -/
def LlmExplain.fiber_contains : Prop :=
  ∀ {I D : Type*} [Fintype I] [DecidableEq I] (v : I → D → ℝ)
    {p c : I → ℝ},
    c ∈ LinearMap.ker (LlmExplain.ambMap v) →
      LlmExplain.attn (fun i => p i + c i) v = LlmExplain.attn p v
        ∧ ∑ i, (p i + c i) = ∑ i, p i

/-- 台账 C28：仿射相关时存在第二个解释（C23 的逆）。 -/
def LlmExplain.exists_second_explanation : Prop :=
  ∀ {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (v : I → D → ℝ),
    ¬ LlmExplain.AffinelyIndependent v →
      ∃ p p' : I → ℝ,
        (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ p' i) ∧
        (∑ i, p i = 1) ∧ (∑ i, p' i = 1) ∧ p ≠ p' ∧
        LlmExplain.attn p v = LlmExplain.attn p' v

end Challenge
