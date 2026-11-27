import Mathlib

/-!
# LlmExplain：注意力架构的精确解释

对应 `docs/SPEC.md` 的定义台账。

对象是**架构类**，不是任何具体训练好的权重：定理里不出现具体参数。

第一个里程碑是精确的结构事实，不是近似：
softmax 是概率分布（C1–C3），注意力输出落在值的范围内（C4），
并且只依赖分差（C5）、对分差单调（C6）。
-/

namespace LlmExplain

variable {I : Type*} [Fintype I] [Nonempty I]

/-- softmax。定义域要求 `I` 非空，否则分母是空和。 -/
noncomputable def softmax (z : I → ℝ) (i : I) : ℝ :=
  Real.exp (z i) / ∑ j, Real.exp (z j)

/-- **台账 C1**：softmax 的分母严格为正（`exp > 0`，且 `I` 非空）。 -/
theorem exp_sum_pos (z : I → ℝ) : 0 < ∑ j, Real.exp (z j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (z j)) Finset.univ_nonempty

/-- **台账 C2**：softmax 的每个分量严格为正。 -/
theorem softmax_pos (z : I → ℝ) (i : I) : 0 < softmax z i :=
  div_pos (Real.exp_pos (z i)) (exp_sum_pos z)

/-- **台账 C3**：softmax 的分量之和为 1。 -/
theorem softmax_sum (z : I → ℝ) : ∑ i, softmax z i = 1 := by
  simp only [softmax]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (exp_sum_pos z))

/-- 注意力输出：以 `p` 为权重对值 `v · d` 加权求和。 -/
noncomputable def attn (p : I → ℝ) (v : I → D → ℝ) (d : D) : ℝ :=
  ∑ i, p i * v i d

/-- **台账 C4**：注意力输出落在值的范围内。

若每个值在第 `d` 维上都不超过 `M`，则输出的第 `d` 维也如此。
证明只用 C2（非负）与 C3（和为 1）——这就是「凸组合」的全部内容。 -/
theorem attn_range (z : I → ℝ) (v : I → D → ℝ) (d : D) {M : ℝ}
    (hv : ∀ i, |v i d| ≤ M) :
    |attn (softmax z) v d| ≤ M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hv (Classical.arbitrary I))
  calc |attn (softmax z) v d| = |∑ i, softmax z i * v i d| := rfl
    _ ≤ ∑ i, |softmax z i * v i d| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, softmax z i * |v i d| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_pos (softmax_pos z i)]
    _ ≤ ∑ i, softmax z i * M :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hv i) (softmax_pos z i).le)
    _ = M := by rw [← Finset.sum_mul, softmax_sum z, one_mul]

/-- **台账 C5**：softmax 只依赖分差——整体平移不改变结果。 -/
theorem softmax_shift (z : I → ℝ) (c : ℝ) :
    softmax (fun i => z i + c) = softmax z := by
  funext i
  have hc : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  simp only [softmax, Real.exp_add]
  rw [← Finset.sum_mul, mul_div_mul_right _ _ hc]

/-- **台账 C6**：softmax 对分差单调。 -/
theorem softmax_mono (z : I → ℝ) {i j : I} (h : z i ≤ z j) :
    softmax z i ≤ softmax z j := by
  simp only [softmax]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h) (exp_sum_pos z).le

end LlmExplain

/-! ## 分差控制：从精确结构到带误差的迁移

softmax 不是分段线性的，所以「精确仿射解释」无法直接给出。
但如果最大分与其余分之间有足够大的 gap，softmax 会集中到最大项上，
于是它可以用**硬注意力**（只取一个值，分段线性）逼近，误差显式可控。

这就是把上一个项目（`~/cnn-explain`）的分段线性理论搬到注意力架构上的那一步。 -/

namespace LlmExplain

namespace Gap

variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]

/-- **台账 C7**：若 `i₀` 是严格最大、其余分都比它低至少 `δ > 0`，
则 `i₀` 的 softmax 权重不小于 `1 / (1 + (|I|-1) e^{-δ})`。 -/
theorem softmax_ge_of_gap (z : I → ℝ) (i₀ : I) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ j, j ≠ i₀ → z j ≤ z i₀ - δ) :
    1 / (1 + ((Fintype.card I : ℝ) - 1) * Real.exp (-δ)) ≤ softmax z i₀ := by
  -- 把 softmax 写成「分母是相对分差的指数和」的形式
  have hne : Real.exp (z i₀) ≠ 0 := (Real.exp_pos _).ne'
  have h1 : softmax z i₀ = (∑ j, Real.exp (z j - z i₀))⁻¹ := by
    have h2 : ∑ j, Real.exp (z j - z i₀)
        = (∑ j, Real.exp (z j)) / Real.exp (z i₀) := by
      simp only [Real.exp_sub]
      rw [Finset.sum_div]
    rw [h2, inv_div]
    rfl
  -- 分母的下界
  have hterm : ∀ j ∈ Finset.univ.erase i₀, Real.exp (z j - z i₀) ≤ Real.exp (-δ) := by
    intro j hj
    have hne' : j ≠ i₀ := Finset.ne_of_mem_erase hj
    exact Real.exp_le_exp.mpr (by linarith [hgap j hne'])
  have hsplit : ∑ j, Real.exp (z j - z i₀)
      = 1 + ∑ j ∈ Finset.univ.erase i₀, Real.exp (z j - z i₀) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
    simp
  have hcard : ((Finset.univ.erase i₀).card : ℝ) = (Fintype.card I : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
    push_cast [this]
    ring
  have hbound : ∑ j ∈ Finset.univ.erase i₀, Real.exp (z j - z i₀)
      ≤ ((Fintype.card I : ℝ) - 1) * Real.exp (-δ) := by
    calc ∑ j ∈ Finset.univ.erase i₀, Real.exp (z j - z i₀)
        ≤ ∑ _j ∈ Finset.univ.erase i₀, Real.exp (-δ) := Finset.sum_le_sum hterm
      _ = ((Finset.univ.erase i₀).card : ℝ) * Real.exp (-δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card I : ℝ) - 1) * Real.exp (-δ) := by rw [hcard]
  have hden : ∑ j, Real.exp (z j - z i₀) ≤ 1 + ((Fintype.card I : ℝ) - 1) * Real.exp (-δ) := by
    rw [hsplit]; linarith
  have hpos : 0 < ∑ j, Real.exp (z j - z i₀) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hpos2 : 0 < 1 + ((Fintype.card I : ℝ) - 1) * Real.exp (-δ) := by
    have := Real.exp_pos (-δ)
    have : 0 ≤ ((Fintype.card I : ℝ) - 1) * Real.exp (-δ) := by
      apply mul_nonneg _ this.le
      have := Fintype.card_pos_iff.mpr ⟨i₀⟩
      push_cast [this]; linarith
    linarith
  rw [h1, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hden

/-- **台账 C8（硬注意力逼近）**：注意力输出与「只取 `i₀` 的值」之差，
不超过 `(1 - p i₀) * 2M`。

这是把分段线性理论搬到注意力上的接合点：硬注意力是选择映射，是分段线性的；
只要 softmax 的权重集中在 `i₀` 上，两者之差就被 `1 - p i₀` 控制。 -/
theorem hard_attn_error (z : I → ℝ) (v : I → D → ℝ) (d : D) (i₀ : I) {M : ℝ}
    (hv : ∀ i, |v i d| ≤ M) :
    |attn (softmax z) v d - v i₀ d| ≤ (1 - softmax z i₀) * (2 * M) := by
  have hsum1 : ∑ j, softmax z j = 1 := softmax_sum z
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hv i₀)
  -- 把差写成加权和
  have hEq : ∑ j, softmax z j * (v j d - v i₀ d)
      = attn (softmax z) v d - v i₀ d := by
    simp only [attn, mul_sub]
    rw [Finset.sum_sub_distrib]
    have hconst : ∑ j, softmax z j * v i₀ d = v i₀ d := by
      rw [← Finset.sum_mul, hsum1, one_mul]
    rw [hconst]
  rw [← hEq]
  calc |∑ j, softmax z j * (v j d - v i₀ d)|
      ≤ ∑ j, |softmax z j * (v j d - v i₀ d)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, softmax z j * |v j d - v i₀ d| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_pos (softmax_pos z j)]
    _ = ∑ j ∈ Finset.univ.erase i₀, softmax z j * |v j d - v i₀ d| := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
        simp
    _ ≤ ∑ j ∈ Finset.univ.erase i₀, softmax z j * (2 * M) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := abs_le.mp (hv j)
        have hi' := abs_le.mp (hv i₀)
        have h2 : |v j d - v i₀ d| ≤ 2 * M := by
          rw [abs_le]
          constructor <;> linarith [hj'.1, hj'.2, hi'.1, hi'.2]
        exact mul_le_mul_of_nonneg_left h2 (softmax_pos z j).le
    _ = (∑ j ∈ Finset.univ.erase i₀, softmax z j) * (2 * M) := by
        rw [Finset.sum_mul]
    _ = (1 - softmax z i₀) * (2 * M) := by
        have hrest : ∑ j ∈ Finset.univ.erase i₀, softmax z j = 1 - softmax z i₀ := by
          have := Finset.sum_erase_add (Finset.univ : Finset I) (softmax z)
            (Finset.mem_univ i₀)
          rw [hsum1] at this
          linarith
        rw [hrest]

end Gap

/-! ## RMSNorm：齐性

**SPEC 里原本写的是 `rmsnorm ε (c • x) = rmsnorm ε x`，这是假的**：
带 `ε > 0` 的分母是 `c * rms x + ε`，不随 `c` 因子化。
真正成立的是 `rms` 的一次齐性（C9）；尺度不变性只在 `ε = 0` 时成立，不列为台账条目。

这次自我修正正对应 SPEC §5 的第 5 条可伪性检验。 -/

section Norm

variable {D : Type*} [Fintype D]

/-- 均方根：`sqrt ((∑ x d ^ 2) / |D|)`。 -/
noncomputable def rms (x : D → ℝ) : ℝ :=
  Real.sqrt ((∑ d, x d ^ 2) / (Fintype.card D : ℝ))

/-- **台账 C9**：`rms` 是一次齐次的——缩放 `c` 倍，`rms` 变成 `|c|` 倍。 -/
theorem rms_smul (x : D → ℝ) (c : ℝ) :
    rms (fun d => c * x d) = |c| * rms x := by
  have h : ∑ d, (c * x d) ^ 2 = c ^ 2 * ∑ d, x d ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp only [rms, h, mul_div_assoc]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

end Norm

/-! ## 残差块：把 C8 从「一个头」抬到「一层」

一个残差块的输出是 `x + 注意力输出`。两件事：
范围界（C10），以及它与「硬注意力 + 残差」这个**分段线性**代理之差（C11）——
后者就是 C8 在层级的版本。 -/

section Block

variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]

/-- 一个残差块：`x ↦ x + 注意力 (z, v)`。 -/
noncomputable def block (z : I → ℝ) (v : I → D → ℝ) (x : D → ℝ) : D → ℝ :=
  fun d => x d + attn (softmax z) v d

/-- **台账 C10**：残差块输出的范围界由「输入的界 + 值的界」控制。 -/
theorem block_range (z : I → ℝ) (v : I → D → ℝ) (x : D → ℝ) {A B : ℝ}
    (hx : ∀ d, |x d| ≤ A) (hv : ∀ i d, |v i d| ≤ B) (d : D) :
    |block z v x d| ≤ A + B := by
  have hb := attn_range z v d (M := B) (fun i => hv i d)
  simp only [block]
  calc |x d + attn (softmax z) v d| ≤ |x d| + |attn (softmax z) v d| := abs_add_le _ _
    _ ≤ A + B := add_le_add (hx d) hb

/-- **台账 C11**：残差块与「硬注意力的残差块」之差，就是 C8 的界。

右边是**分段线性**的（`x d + v i₀ d` 对 `x` 是仿射，对 `i₀` 的选择是分段常值），
所以这条说：整个块可以用一个分段线性映射逼近，误差 `(1 - p i₀) · 2M` 显式可控。 -/
theorem block_close_to_hard (z : I → ℝ) (v : I → D → ℝ) (x : D → ℝ) (d : D)
    (i₀ : I) {M : ℝ} (hv : ∀ i, |v i d| ≤ M) :
    |block z v x d - (x d + v i₀ d)| ≤ (1 - softmax z i₀) * (2 * M) := by
  have h := Gap.hard_attn_error z v d i₀ hv
  simp only [block]
  rw [show x d + attn (softmax z) v d - (x d + v i₀ d)
      = attn (softmax z) v d - v i₀ d by ring]
  exact h

end Block

/-! ## 猜想：注意力头是梯度映射

`softmax` 作为 `z` 的映射是单调的（它是凸函数 `logsumexp` 的梯度——这一步是
经典事实，**本工程不定义 `logsumexp`、也不形式化它**）。形式化的是下面这条不等式：

  `⟨softmax z − softmax z', z − z'⟩ ≥ 0`

证明走 Gibbs 不等式：右边等于两个 KL 散度之和。 -/

section Gradient

variable {I : Type*} [Fintype I] [Nonempty I]

/-- softmax 的对数等于分数减去配分函数的对数。 -/
theorem log_softmax (z : I → ℝ) (i : I) :
    Real.log (softmax z i) = z i - Real.log (∑ j, Real.exp (z j)) := by
  have hZ : (0:ℝ) < ∑ j, Real.exp (z j) := exp_sum_pos z
  simp only [softmax]
  rw [Real.log_div (Real.exp_pos (z i)).ne' hZ.ne', Real.log_exp]

/-- **Gibbs 不等式**：KL 散度非负。

对每个 `i` 用 `log (q/p) ≤ q/p − 1`，乘 `p > 0` 后求和。 -/
theorem kl_nonneg (z z' : I → ℝ) :
    0 ≤ ∑ i, softmax z i * Real.log (softmax z i / softmax z' i) := by
  have key : ∀ i, softmax z i - softmax z' i
      ≤ softmax z i * Real.log (softmax z i / softmax z' i) := by
    intro i
    have hp := softmax_pos z i
    have hq := softmax_pos z' i
    have hqp : 0 < softmax z' i / softmax z i := div_pos hq hp
    have h1 : Real.log (softmax z' i / softmax z i) ≤ softmax z' i / softmax z i - 1 :=
      Real.log_le_sub_one_of_pos hqp
    have h2 : Real.log (softmax z i / softmax z' i)
        = - Real.log (softmax z' i / softmax z i) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [h2, mul_neg]
    have := mul_le_mul_of_nonneg_left h1 hp.le
    have hsimpl : softmax z i * (softmax z' i / softmax z i - 1)
        = softmax z' i - softmax z i := by
      field_simp
    linarith [this, hsimpl]
  have hsum : ∑ i, (softmax z i - softmax z' i) = 0 := by
    rw [Finset.sum_sub_distrib, softmax_sum, softmax_sum, sub_self]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [hsum] at this
  exact this

/-- **台账 C12（注意力头是梯度映射）**：`⟨p − p', z − z'⟩ ≥ 0`。

它等于 `KL(p‖p') + KL(p'‖p)`，由 C13（Gibbs）非负。
因此注意力头**不能反向选择**——没有任何权重能让它逆着分数差移动。 -/
theorem softmax_monotone (z z' : I → ℝ) :
    0 ≤ ∑ i, (softmax z i - softmax z' i) * (z i - z' i) := by
  -- z i - z' i = log(p i) - log(p' i) + (log Z - log Z')
  have hdecomp : ∀ i, z i - z' i
      = Real.log (softmax z i / softmax z' i)
        + (Real.log (∑ j, Real.exp (z j)) - Real.log (∑ j, Real.exp (z' j))) := by
    intro i
    have h1 := log_softmax z i
    have h2 := log_softmax z' i
    rw [Real.log_div (softmax_pos z i).ne' (softmax_pos z' i).ne']
    linarith
  have hzero : ∑ i, (softmax z i - softmax z' i) = 0 := by
    rw [Finset.sum_sub_distrib, softmax_sum, softmax_sum, sub_self]
  have hstep1 : ∑ i, (softmax z i - softmax z' i) * (z i - z' i)
      = ∑ i, (softmax z i - softmax z' i) * Real.log (softmax z i / softmax z' i) := by
    have hterm : ∀ i, (softmax z i - softmax z' i) * (z i - z' i)
        = (softmax z i - softmax z' i) * Real.log (softmax z i / softmax z' i)
          + (softmax z i - softmax z' i)
            * (Real.log (∑ j, Real.exp (z j)) - Real.log (∑ j, Real.exp (z' j))) := by
      intro i
      rw [hdecomp i]
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      Finset.sum_add_distrib]
    have hconst : ∑ i, (softmax z i - softmax z' i)
        * (Real.log (∑ j, Real.exp (z j)) - Real.log (∑ j, Real.exp (z' j))) = 0 := by
      rw [← Finset.sum_mul, hzero, zero_mul]
    rw [hconst, add_zero]
  have hstep2 : ∑ i, (softmax z i - softmax z' i) * Real.log (softmax z i / softmax z' i)
      = (∑ i, softmax z i * Real.log (softmax z i / softmax z' i))
        + (∑ i, softmax z' i * Real.log (softmax z' i / softmax z i)) := by
    have hterm : ∀ i, (softmax z i - softmax z' i) * Real.log (softmax z i / softmax z' i)
        = softmax z i * Real.log (softmax z i / softmax z' i)
          + softmax z' i * Real.log (softmax z' i / softmax z i) := by
      intro i
      have hinv : Real.log (softmax z' i / softmax z i)
          = - Real.log (softmax z i / softmax z' i) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [hinv]
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      Finset.sum_add_distrib]
  rw [hstep1, hstep2]
  linarith [kl_nonneg z z', kl_nonneg z' z]

/-- **台账 C13（雅可比是协方差）**：softmax 的线性响应不是任意矩阵，而是协方差。

具体地，对任意 `a`，加权方差非负：
`(∑ p i * a i)^2 ≤ ∑ p i * (a i)^2`。

**只证了这一条标量不等式。** "一阶敏感度 `∂p_i/∂z_j = p_i(δ_ij − p_j)` 对称半正定、
行和为零、秩 ≤ `|I| − 1`"是正确的数学，但**未形式化**——本工程没有定义雅可比。 -/
theorem softmax_variance_nonneg (z : I → ℝ) (a : I → ℝ) :
    (∑ i, softmax z i * a i) ^ 2 ≤ ∑ i, softmax z i * a i ^ 2 := by
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => Real.sqrt (softmax z i)) (fun i => Real.sqrt (softmax z i) * a i)
  have h1 : ∀ i : I, Real.sqrt (softmax z i) * (Real.sqrt (softmax z i) * a i)
      = softmax z i * a i := by
    intro i
    rw [← mul_assoc, Real.mul_self_sqrt (softmax_pos z i).le]
  have h2 : ∀ i : I, (Real.sqrt (softmax z i)) ^ 2 = softmax z i := fun i =>
    Real.sq_sqrt (softmax_pos z i).le
  have h3 : ∀ i : I, (Real.sqrt (softmax z i) * a i) ^ 2 = softmax z i * a i ^ 2 := by
    intro i
    rw [mul_pow, Real.sq_sqrt (softmax_pos z i).le]
  simpa only [h1, h2, h3, softmax_sum, one_mul] using hcauchy

end Gradient

/-! ## 复合：值路径稳定，分数路径不稳定

「复合之后梯度结构还在吗」这个问题，能确切回答的是两条：

* **值路径**（value path）是非扩张的：改变值向量，输出最多按同样幅度变化。
  这不需要任何权重条件。
* **分数路径**（score path）没有这样的界：`z` 进入 softmax 之前已经过
  `QK^T/√d`，那里的放大率没有上界。

所以残差网络对值的扰动是稳定的（C15），对分数的扰动不是——
这正是"梯度结构是单头性质、不随复合保持"的具体形态。 -/

section ValuePath

variable {I : Type*} [Fintype I] [Nonempty I]

/-- **台账 C14**：注意力输出对值是 1-Lipschitz 的（sup 范数意义）。

`|attn v − attn v'| ≤ M` 当每个坐标的差都不超过 `M`。
证明只用权重非负且和为 1——与权重具体是什么无关。 -/
theorem attn_value_lipschitz (z : I → ℝ) (v v' : I → D → ℝ) (d : D) {M : ℝ}
    (hv : ∀ i, |v i d - v' i d| ≤ M) :
    |attn (softmax z) v d - attn (softmax z) v' d| ≤ M := by
  have hEq : attn (softmax z) v d - attn (softmax z) v' d
      = ∑ i, softmax z i * (v i d - v' i d) := by
    simp only [attn, mul_sub, Finset.sum_sub_distrib]
  rw [hEq]
  calc |∑ i, softmax z i * (v i d - v' i d)|
      ≤ ∑ i, |softmax z i * (v i d - v' i d)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, softmax z i * |v i d - v' i d| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_pos (softmax_pos z i)]
    _ ≤ ∑ i, softmax z i * M :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (softmax_pos z i).le)
    _ = M := by rw [← Finset.sum_mul, softmax_sum z, one_mul]

/-- **台账 C15**：残差块对（残差, 值）的联合 Lipschitz 界——

`|B(x,v) − B(x',v')| ≤ |x − x'| + M`（分数固定）。

界是**相加**的，不是相乘：深度增加时残差路径线性增长，不会指数放大。 -/
theorem block_lipschitz (z : I → ℝ) (x x' : D → ℝ) (v v' : I → D → ℝ) (d : D) {M : ℝ}
    (hv : ∀ i, |v i d - v' i d| ≤ M) :
    |block z v x d - block z v' x' d| ≤ |x d - x' d| + M := by
  have hval := attn_value_lipschitz z v v' d hv
  have hEq : block z v x d - block z v' x' d
      = (x d - x' d) + (attn (softmax z) v d - attn (softmax z) v' d) := by
    simp only [block]
    ring
  rw [hEq]
  exact le_trans (abs_add_le _ _) (add_le_add (le_refl _) hval)

end ValuePath

/-! ## 为什么偏偏是 softmax：唯一性的核心

不是"softmax 恰好是概率分布"，而是**只有一类机制同时满足两条要求**：

* （逐点）权重只由每个分数经同一个函数 `f` 得到，再归一化；
* （平移不变）所有分数同加一个常数，权重不变。

两位置情形的权重是 `f a / (f a + f b)`。平移不变性要求
`f(a+c)/(f(a+c)+f(b+c)) = f a/(f a + f b)`，交叉相乘后中间项相消，得到

  `f(a+c) · f b = f a · f(b+c)`，

取 `b = 0` 就是乘性 Cauchy 方程 `f(a+c) · f 0 = f a · f c`。
它的正则解就是指数函数——于是权重必然是带温度的 softmax。

下面证这个方程（C16）、以及指数族确实满足它（C17）。
"正则解都是指数"属于经典 Cauchy 理论，本工程不重证，记在 SPEC 里。 -/

section Uniqueness

/-- 两位置的逐点注意力权重：`f a / (f a + f b)`。 -/
noncomputable def weight2 (f : ℝ → ℝ) (a b : ℝ) : ℝ := f a / (f a + f b)

/-- **台账 C16**：平移不变性迫使乘性 Cauchy 方程。

这是"为什么是 softmax"的核心一步：不是任意函数都能当权重生成器。 -/
theorem shift_inv_forces_multiplicative (f : ℝ → ℝ) (hf : ∀ x, 0 < f x)
    (h : ∀ a b c, weight2 f (a + c) (b + c) = weight2 f a b) :
    ∀ a b c, f (a + c) * f b = f a * f (b + c) := by
  intro a b c
  have h1 : f (a + c) + f (b + c) ≠ 0 := by
    have := hf (a + c); have := hf (b + c); linarith
  have h2 : f a + f b ≠ 0 := by
    have := hf a; have := hf b; linarith
  have key := h a b c
  simp only [weight2] at key
  rw [div_eq_div_iff h1 h2] at key
  linarith [key]

/-- 取 `b = 0`：`f(a+c) · f 0 = f a · f c`，即 `g(a+c) = g a · g c`（`g = f/f 0`）。 -/
theorem shift_inv_cauchy (f : ℝ → ℝ) (hf : ∀ x, 0 < f x)
    (h : ∀ a b c, weight2 f (a + c) (b + c) = weight2 f a b) (a c : ℝ) :
    f (a + c) * f 0 = f a * f c := by
  simpa using shift_inv_forces_multiplicative f hf h a 0 c

/-- **台账 C17**：指数族满足平移不变性——softmax（任意温度）都是解。

`exp (λ (a+c)) = exp (λ a) · exp (λ c)`，公因子约掉。 -/
theorem exp_weight_shift_invariant (lam : ℝ) :
    ∀ a b c, weight2 (fun x => Real.exp (lam * x)) (a + c) (b + c)
      = weight2 (fun x => Real.exp (lam * x)) a b := by
  intro a b c
  have hfac : ∀ x : ℝ, Real.exp (lam * (x + c)) = Real.exp (lam * x) * Real.exp (lam * c) := by
    intro x
    rw [mul_add, Real.exp_add]
  have hc : 0 < Real.exp (lam * c) := Real.exp_pos _
  have hden : Real.exp (lam * a) * Real.exp (lam * c)
      + Real.exp (lam * b) * Real.exp (lam * c)
      = (Real.exp (lam * a) + Real.exp (lam * b)) * Real.exp (lam * c) := by ring
  simp only [weight2, hfac, hden]
  rw [mul_div_mul_right _ _ hc.ne']

end Uniqueness

/-! ## 深度的代数来源

**没有残差、没有非线性时，深度是假的。** 一个线性注意力层是 `X ↦ P · X · W`；
两层复合仍是同一形状，只是 `P` 与 `W` 各自相乘。归纳下去，任意深度塌缩成**一层**。

**残差是唯一让深度不塌缩的东西**：`(1+A)(1+B) = 1 + A + B + A·B`，
交叉项 `A·B` 是深度贡献的、单层拿不到的那部分。

这两条合起来回答"为什么需要残差"。 -/

section Depth

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I] [DecidableEq D]

/-- 线性注意力层：`X ↦ P · X · W`。 -/
def linLayer (P : Matrix I I ℝ) (W : Matrix D D ℝ) (X : Matrix I D ℝ) : Matrix I D ℝ :=
  P * X * W

/-- **台账 C20：深度塌缩。** 两个线性注意力层的复合还是一个线性注意力层。 -/
theorem linLayer_comp (P₂ P₁ : Matrix I I ℝ) (W₁ W₂ : Matrix D D ℝ)
    (X : Matrix I D ℝ) :
    linLayer P₂ W₂ (linLayer P₁ W₁ X) = linLayer (P₂ * P₁) (W₁ * W₂) X := by
  simp only [linLayer, Matrix.mul_assoc]

/-- **台账 C21：残差产生交叉项。** `(1+A)(1+B) = 1 + A + B + A·B`——
`A·B` 是单层拿不到、只有深度才产生的项。 -/
theorem residual_cross_term (A B : Matrix I I ℝ) :
    (1 + A) * (1 + B) = 1 + A + B + A * B := by
  noncomm_ring

end Depth

/-! ## 注意力是严格收缩的

这是整个项目里唯一一条**动力学**结论，也是"为什么必须要有残差"的真正回答。

设权重矩阵每行是概率分布（和为 1，每项 ≥ `m`）。则对任意两个位置 `i, j`，
它们的（加权）输出之差不超过 `(1 − |I|·m)` 乘以值的跨度。由于 softmax 的每个权重
严格为正（C2），`m > 0`，所以**因子严格小于 1**——每一层都在收缩。

反复叠加，token 之间的距离指数衰减（这就是 rank collapse），残差是唯一的对抗项。 -/

section Contraction

variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]

/-- 一维差的绝对值等于和减两倍最小值——把 `ℓ¹` 距离换成「重叠度」。 -/
theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- **台账 C22（注意力是严格收缩的）**。

若权重矩阵的每行和为 1、每项 ≥ `m`（`m ≥ 0`），且值都在 `c` 的 `D/2` 邻域内，
则任意两个位置的输出之差不超过 `(1 − |I|·m) · D`。

**关键**：softmax 的权重严格为正（C2），所以 `m > 0`，因子 `1 − |I|·m < 1`——
收缩是无条件的，不需要任何关于权重的假设。 -/
theorem attention_contracts (p : I → I → ℝ) (m : ℝ) (hp : ∀ i k, m ≤ p i k) (hm : 0 ≤ m)
    (hrow : ∀ i, ∑ k, p i k = 1) (v : I → ℝ) (c D : ℝ)
    (hv : ∀ k, |v k - c| ≤ D / 2) (i j : I) :
    |∑ k, p i k * v k - ∑ k, p j k * v k|
      ≤ (1 - (Fintype.card I : ℝ) * m) * D := by
  -- 常数项消掉：∑ (p_i − p_j) = 0
  have hzero : ∑ k, (p i k - p j k) = 0 := by
    rw [Finset.sum_sub_distrib, hrow i, hrow j, sub_self]
  have hsplit : ∑ k, p i k * v k - ∑ k, p j k * v k
      = ∑ k, (p i k - p j k) * (v k - c) := by
    have h1 : ∑ k, (p i k - p j k) * (v k - c)
        = ∑ k, (p i k * v k - p j k * v k) - c * ∑ k, (p i k - p j k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h1, hzero, mul_zero, sub_zero, Finset.sum_sub_distrib]
  rw [hsplit]
  -- ℓ¹ 距离 ≤ 2 (1 − |I| m)
  have hcard : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hl1 : ∑ k, |p i k - p j k| ≤ 2 * (1 - (Fintype.card I : ℝ) * m) := by
    have habs : ∀ k, |p i k - p j k| = p i k + p j k - 2 * min (p i k) (p j k) :=
      fun k => abs_sub_eq_add_sub_two_min _ _
    have hsum_abs : ∑ k, |p i k - p j k|
        = 2 - 2 * ∑ k, min (p i k) (p j k) := by
      rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => habs k)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrow i, hrow j,
        Finset.mul_sum]
      ring
    have hmin : (Fintype.card I : ℝ) * m ≤ ∑ k, min (p i k) (p j k) := by
      have : ∑ k : I, m ≤ ∑ k : I, min (p i k) (p j k) := by
        apply Finset.sum_le_sum
        intro k _
        exact le_min (hp i k) (hp j k)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    rw [hsum_abs]
    linarith
  -- 组合
  calc |∑ k, (p i k - p j k) * (v k - c)|
      ≤ ∑ k, |(p i k - p j k) * (v k - c)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |p i k - p j k| * |v k - c| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul]
    _ ≤ ∑ k, |p i k - p j k| * (D / 2) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hv k) (abs_nonneg _))
    _ = (∑ k, |p i k - p j k|) * (D / 2) := by rw [Finset.sum_mul]
    _ ≤ 2 * (1 - (Fintype.card I : ℝ) * m) * (D / 2) := by
        apply mul_le_mul_of_nonneg_right hl1
        linarith [hv i, abs_nonneg (v i - c)]
    _ = (1 - (Fintype.card I : ℝ) * m) * D := by ring

end Contraction

/-! ## 反问题：注意力是可逆的吗

到现在为止的每一条都是"给权重，问输出"。反过来问一次：
**给定输出与值向量，能否唯一确定权重？**

答案是一个充要条件：**当且仅当值向量仿射无关**。

这不是界，是刻画。它的意义是可解释性的：注意力的"权重图"是模型的输出里
**唯一可恢复**的信息之一——但前提是值向量张成足够大的仿射空间。 -/

section Identifiable

variable {I D : Type*} [Fintype I] [DecidableEq I]

/-- 把权重映到「输出 + 权重和」的线性映射。**仿射无关正是它单射**。 -/
noncomputable def ambMap (v : I → D → ℝ) : (I → ℝ) →ₗ[ℝ] ((D → ℝ) × ℝ) :=
  { toFun := fun c => (fun d => ∑ i, c i * v i d, ∑ i, c i)
    map_add' := by
      intro a b
      refine Prod.ext ?_ ?_
      · funext d
        simp [add_mul, Finset.sum_add_distrib]
      · simp [Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      refine Prod.ext ?_ ?_
      · funext d
        simp [Finset.mul_sum, mul_assoc]
      · simp [Finset.mul_sum] }

@[simp] lemma ambMap_apply (v : I → D → ℝ) (c : I → ℝ) :
    ambMap v c = (fun d => ∑ i, c i * v i d, ∑ i, c i) := rfl

/-- 仿射无关，以"零组合只有零解"的形式写出：
若 `∑ c_i v_i = 0` 且 `∑ c_i = 0`，则所有 `c_i = 0`。 -/
def AffinelyIndependent (v : I → D → ℝ) : Prop :=
  ∀ c : I → ℝ, (∀ d, ∑ i, c i * v i d = 0) → (∑ i, c i = 0) → ∀ i, c i = 0

/-- **台账 C23（注意力的可逆性）**：值向量仿射无关时，输出唯一确定权重。

注意这只是**单射**：`attn` 在权重单纯形上是单射。反过来（每个点都能被达到）不成立——
输出在值向量的凸包内，不是每个点都可达。 -/
theorem attn_injective (v : I → D → ℝ) (hind : AffinelyIndependent v)
    {p p' : I → ℝ} (hp : ∑ i, p i = 1) (hp' : ∑ i, p' i = 1)
    (h : attn p v = attn p' v) : p = p' := by
  have hc : ∀ d, ∑ i, (p i - p' i) * v i d = 0 := by
    intro d
    have hd := congrFun h d
    simp only [attn] at hd
    have hsplit : ∑ i, (p i - p' i) * v i d
        = ∑ i, p i * v i d - ∑ i, p' i * v i d := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, hd, sub_self]
  have hsum : ∑ i, (p i - p' i) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hp', sub_self]
  have hzero := hind (fun i => p i - p' i) hc hsum
  funext i
  have := hzero i
  linarith

/-- **台账 C25（长序列不可逆）**：仿射无关要求 `|I| ≤ |D| + 1`。

证明：`c ↦ (d ↦ ∑ c_i v_i d, ∑ c_i)` 是线性映射，仿射无关恰好说它单射；
单射 ⇒ 定义域维数 ≤ 值域维数，即 `|I| ≤ |D| + 1`。

**含义**：位置数超过特征维数加一时，任何一组值向量都仿射相关，
于是（由 C23）**注意力权重不可从输出恢复**。真实 transformer 里 `n > d` 是常态，
所以长序列的注意力图原则上不可反推。 -/
theorem card_le_of_affinelyIndependent [Fintype D] (v : I → D → ℝ)
    (hind : AffinelyIndependent v) : Fintype.card I ≤ Fintype.card D + 1 := by
  classical
  let Φ := ambMap v
  have hinj : Function.Injective Φ := by
    intro c c' hcc
    have hzero : Φ (c - c') = 0 := by
      rw [map_sub, hcc, sub_self]
    have h1 : ∀ d, ∑ j, (c - c') j * v j d = 0 := by
      intro d
      have hfst := congrArg Prod.fst hzero
      have hd := congrFun hfst d
      simpa [Φ, ambMap] using hd
    have h2 : ∑ j, (c - c') j = 0 := by
      have hsnd := congrArg Prod.snd hzero
      simpa [Φ, ambMap] using hsnd
    have hzero' := hind (fun j => (c - c') j) h1 h2
    funext i
    have := hzero' i
    exact sub_eq_zero.mp this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, Module.finrank_self] at hdim
  simpa using hdim

/-- **台账 C26（模糊度的维数）**：与给定输出相容的权重组，构成一个至少
`|I| − (|D| + 1)` 维的仿射子空间。

秩-零化度：`把权重映到 (输出, 权重和)` 的映射，其核的维数 = `|I| − rank`，
而 rank ≤ `|D| + 1`。所以只要上下文比模型宽度长，模糊度就是**高维的**，
不是"另有一个解"，而是"有一整族解"。 -/
theorem ker_finrank_ge [Fintype D] (v : I → D → ℝ) :
    Fintype.card I - (Fintype.card D + 1) ≤ Module.finrank ℝ (LinearMap.ker (ambMap v)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (ambMap v)
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := Submodule.finrank_le (LinearMap.range (ambMap v))
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self] at h2
  omega

/-- **台账 C27**：往权重上加核里的任何向量，输出与权重和都不变。

这条把 C26 的维数变成**实际的模糊**：不只是"存在另一个解"，而是沿整个核方向都解。
对用户的可解释性含义：热图不唯一，而且不唯一的程度是可以算出来的。 -/
theorem fiber_contains (v : I → D → ℝ) {p c : I → ℝ}
    (hc : c ∈ LinearMap.ker (ambMap v)) :
    attn (fun i => p i + c i) v = attn p v
      ∧ ∑ i, (p i + c i) = ∑ i, p i := by
  have h := hc
  rw [LinearMap.mem_ker] at h
  simp only [ambMap_apply, Prod.ext_iff, funext_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : ∀ d, ∑ i, c i * v i d = 0 := by
    intro d
    have := h1 d
    simpa using this
  have h2' : ∑ i, c i = 0 := by simpa using h2
  constructor
  · funext d
    simp only [attn]
    have hsplit : ∑ i, (p i + c i) * v i d
        = ∑ i, p i * v i d + ∑ i, c i * v i d := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, h1' d, add_zero]
  · rw [Finset.sum_add_distrib, h2', add_zero]

/- **台账 C28（C23 的逆）**：仿射相关时，**存在两个不同的概率向量**给出相同输出。

证明：取一条非零的零组合 `c`（`∑ c = 0`、`∑ c_i v_i = 0`），从均匀权 `1/|I|` 出发
沿 `c` 走一小步 `ε`，仍然非负、仍然和为 1，而输出不变。

这条补上了 C23 的另一半，使"当且仅当"成为**机器验证**的充要条件。 -/
end Identifiable

section SecondExplanation

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem exists_second_explanation (v : I → D → ℝ) (h : ¬ AffinelyIndependent v) :
    ∃ p p' : I → ℝ,
      (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ p' i) ∧
      (∑ i, p i = 1) ∧ (∑ i, p' i = 1) ∧ p ≠ p' ∧ attn p v = attn p' v := by
  classical
  simp only [AffinelyIndependent, not_forall] at h
  push_neg at h
  obtain ⟨c, hcv, hcs, hne⟩ := h
  obtain ⟨i0, hi0⟩ := hne
  set n : ℝ := (Fintype.card I : ℝ) with hn
  have hnpos : 0 < n := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i0⟩
    simp only [hn]; exact_mod_cast this
  have hnne : n ≠ 0 := ne_of_gt hnpos
  set C : ℝ := ∑ i, |c i| with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  set ε : ℝ := 1 / (2 * n * (C + 1)) with hε
  have hden : 0 < 2 * n * (C + 1) := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεC : ε * (2 * n * (C + 1)) = 1 := by rw [hε]; field_simp
  have hbound : ∀ i, ε * |c i| < 1 / n := by
    intro i
    have hle : |c i| ≤ C :=
      Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg (c j))
        (Finset.mem_univ i)
    have hmul : ε * |c i| ≤ ε * C := mul_le_mul_of_nonneg_left hle hεpos.le
    have hlt' : ε * C * n < 1 := by
      nlinarith [hεC, hC, hεpos, hnpos, mul_pos hεpos hnpos]
    have hlt : ε * C < 1 / n := (lt_div_iff₀ hnpos).mpr hlt' 
    exact lt_of_le_of_lt hmul hlt
  refine ⟨fun _ => 1 / n, fun i => 1 / n + ε * c i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; positivity
  · intro i
    have h1 : -(ε * |c i|) ≤ ε * c i := by
      have := neg_abs_le (c i); nlinarith
    have h2 := hbound i
    have h3 : (0:ℝ) < 1 / n := by positivity
    nlinarith
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    field_simp
  · have h1 : ∑ i : I, (1 / n + ε * c i) = ∑ i : I, (1 / n) + ε * ∑ i : I, c i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [h1, hcs, mul_zero, add_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    field_simp
  · intro hp
    have hh : (1:ℝ) / n = 1 / n + ε * c i0 := congrFun hp i0
    have hc0 : ε * c i0 = 0 := by linarith
    rcases mul_eq_zero.mp hc0 with h1 | h2
    · exact absurd h1 (ne_of_gt hεpos)
    · exact hi0 h2
  · ext d
    simp only [attn]
    have hsplit : ∑ i, (1 / n + ε * c i) * v i d
        = ∑ i, (1 / n) * v i d + ε * ∑ i, c i * v i d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, hcv d, mul_zero, add_zero]

end SecondExplanation



section ShiftConverse

variable {I : Type*} [Fintype I] [Nonempty I]

/-- **台账 C24（C5 的逆）**：两个 softmax 相同，当且仅当分数只差一个常数。

C5 说的是"整体平移不改变 softmax"；这里是反向：**不差常数就必然不同**。
两者合起来说明 softmax 把分数精确地商掉一个自由度——这正是"只依赖分差"的完整含义。 -/
theorem softmax_eq_iff_shift {z z' : I → ℝ} (h : softmax z = softmax z') :
    ∃ c, ∀ i, z' i = z i + c := by
  refine ⟨Real.log (∑ j, Real.exp (z' j)) - Real.log (∑ j, Real.exp (z j)), fun i => ?_⟩
  have hlog : Real.log (softmax z i) = Real.log (softmax z' i) := by
    rw [show softmax z i = softmax z' i from congrFun h i]
  have h1 := log_softmax z i
  have h2 := log_softmax z' i
  linarith

end ShiftConverse



end LlmExplain
