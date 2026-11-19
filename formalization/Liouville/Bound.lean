import Mathlib

/-!
# `prop:bound` —— 反向一致界（机器验证部分）

论文 A（`paperA/mainA.tex`，`\label{prop:bound}`）的陈述是：

    Under (H₁)–(H₃) and (eq:axis), with R as in (eq:R),
      |Φ(t,ρ,ζ)| ≤ C₁ / (2 (1 + √(-t)))   for all ρ, ζ, t ≤ 0.

**本文档验证的是它的最后一步**，即论文证明里的两行：

    |Γ(t,ρ,ζ)| ≤ ∫₀^ρ C₁ρ'/R dρ' ≤ C₁ρ² / (2(1+√(-t)))，再除以 ρ²。

前置的一步 `∂_ρΓ = ρω^ζ` 且 `|ω^ζ| ≤ |ω| ≤ C₁/R`（由 (H2)）在这里作为**假设**
`hbound` 给出；它需要 ℝ³ 的旋度与柱坐标链式法则，不在本次机器验证的范围内。
这一步的缺失意味着：本文件证明的是 `prop:bound` 的**条件版本**，
台账里记为 `A9a`（状态 `PROVED`），`A9`（整条 `prop:bound`）保持 `PROVED-INFORMAL`。

定义与论文逐字对应：

* `R ρ ζ t = 1 + √(ρ²+ζ²) + √(-t)`，即 (eq:R) 在轴对称下的形式（`|x| = √(ρ²+ζ²)`）。
  注意**没有**简化成 `1+ρ+√(-t)`：那会让 R 变小、假设变强。
* `Δ_μ` 不在这里出现。`Phi = Γ/ρ²` 即 (eq:Phi)。
-/

open Real Set Filter MeasureTheory
open scoped Interval

namespace Liouville

noncomputable section

/-- (eq:R)：`R(x,t) = 1 + |x| + √(-t)`，轴对称下 `|x| = √(ρ²+ζ²)`。 -/
def R (ρ ζ t : ℝ) : ℝ := 1 + Real.sqrt (ρ ^ 2 + ζ ^ 2) + Real.sqrt (-t)

/-- (eq:Phi)：提升后的涡量 `Φ = Γ/ρ²`。 -/
def Phi (Γ : ℝ → ℝ → ℝ → ℝ) (ρ ζ t : ℝ) : ℝ := Γ ρ ζ t / ρ ^ 2

/-- (eq:identities)：`ω^ζ = Γ_ρ/ρ`。 -/
def omegaZeta (Γ : ℝ → ℝ → ℝ → ℝ) (ρ ζ t : ℝ) : ℝ :=
  deriv (fun r => Γ r ζ t) ρ / ρ

lemma R_ge (ρ ζ t : ℝ) : 1 + Real.sqrt (-t) ≤ R ρ ζ t := by
  unfold R
  have := Real.sqrt_nonneg (ρ ^ 2 + ζ ^ 2)
  linarith

lemma R_pos (ρ ζ t : ℝ) : 0 < R ρ ζ t := by
  have h1 := Real.sqrt_nonneg (ρ ^ 2 + ζ ^ 2)
  have h2 := Real.sqrt_nonneg (-t)
  unfold R; linarith

lemma one_add_sqrt_pos (t : ℝ) : 0 < 1 + Real.sqrt (-t) := by
  have := Real.sqrt_nonneg (-t)
  linarith

/-- (eq:identities)：`ρ ω^ζ = ∂_ρ Γ`。这是定义层面的直接改写，不含分析内容。 -/
theorem rho_mul_omegaZeta (Γ : ℝ → ℝ → ℝ → ℝ) (ρ ζ t : ℝ) (hρ : ρ ≠ 0) :
    ρ * omegaZeta Γ ρ ζ t = deriv (fun r => Γ r ζ t) ρ := by
  unfold omegaZeta
  field_simp

/-! ## 积分估计：`|Γ| ≤ C₁ρ²/(2(1+√-t))`

常数 `1/2` 与论文逐字一致：`1/R ≤ 1/(1+√-t)` 是**逐点**代入后被积分的，
不是把被积函数换成上确界再乘 ρ（那会多出一个因子 2）。 -/

theorem abs_Gamma_le (Γ : ℝ → ℝ → ℝ → ℝ) (C₁ ζ t ρ : ℝ)
    (hC₁ : 0 ≤ C₁) (hρ : 0 ≤ ρ)
    (hΓ0 : Γ 0 ζ t = 0)
    (hdiff : ∀ x, 0 ≤ x → DifferentiableAt ℝ (fun r => Γ r ζ t) x)
    (hint : IntervalIntegrable (deriv (fun r => Γ r ζ t)) volume 0 ρ)
    (hbound : ∀ r ∈ Icc 0 ρ, |deriv (fun r => Γ r ζ t) r| ≤ C₁ * r / R r ζ t) :
    |Γ ρ ζ t| ≤ C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by
  -- 微积分基本定理：Γ ρ - Γ 0 = ∫₀^ρ Γ'
  have hdiff' : ∀ x ∈ uIcc 0 ρ, DifferentiableAt ℝ (fun r => Γ r ζ t) x := by
    intro x hx
    rw [uIcc_of_le hρ] at hx
    exact hdiff x hx.1
  have hfund : ∫ r in (0)..ρ, deriv (fun r => Γ r ζ t) r = Γ ρ ζ t - Γ 0 ζ t :=
    intervalIntegral.integral_deriv_eq_sub hdiff' hint
  -- 逐点界，分母换成与 r 无关的常数
  have hpt : ∀ r ∈ Ioc 0 ρ, ‖deriv (fun r => Γ r ζ t) r‖ ≤
      C₁ * r / (1 + Real.sqrt (-t)) := by
    intro r hr
    rw [Real.norm_eq_abs]
    have hr0 : 0 ≤ r := le_of_lt hr.1
    have hle := hbound r (Ioc_subset_Icc_self hr)
    have hRge : 1 + Real.sqrt (-t) ≤ R r ζ t := R_ge r ζ t
    have hpos : 0 < 1 + Real.sqrt (-t) := one_add_sqrt_pos t
    have h1 : C₁ * r / R r ζ t ≤ C₁ * r / (1 + Real.sqrt (-t)) :=
      div_le_div_of_nonneg_left (mul_nonneg hC₁ hr0) hpos hRge
    linarith
  -- 比较函数的区间可积性
  have hg : IntervalIntegrable (fun r => C₁ * r / (1 + Real.sqrt (-t))) volume 0 ρ := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- 积分估计
  have hmain : ‖∫ r in (0)..ρ, deriv (fun r => Γ r ζ t) r‖ ≤
      ∫ r in (0)..ρ, C₁ * r / (1 + Real.sqrt (-t)) :=
    intervalIntegral.norm_integral_le_of_norm_le hρ (Eventually.of_forall hpt) hg
  -- 比较积分求值
  have hInt : ∫ r in (0)..ρ, C₁ * r / (1 + Real.sqrt (-t)) =
      C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by
    have hfun : (fun r => C₁ * r / (1 + Real.sqrt (-t)))
        = (fun r => (C₁ / (1 + Real.sqrt (-t))) * r) := by
      funext r; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_id]
    norm_num
    field_simp
  calc |Γ ρ ζ t| = |∫ r in (0)..ρ, deriv (fun r => Γ r ζ t) r| := by
        rw [hfund, hΓ0, sub_zero]
    _ = ‖∫ r in (0)..ρ, deriv (fun r => Γ r ζ t) r‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ r in (0)..ρ, C₁ * r / (1 + Real.sqrt (-t)) := hmain
    _ = C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := hInt

/-! ## 除以 ρ² -/

theorem abs_Phi_le (Γ : ℝ → ℝ → ℝ → ℝ) (C₁ ζ t : ℝ) (hC₁ : 0 ≤ C₁)
    (hΓ0 : Γ 0 ζ t = 0)
    (h : ∀ ρ, 0 ≤ ρ → |Γ ρ ζ t| ≤ C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t)))) :
    ∀ ρ, 0 ≤ ρ → |Phi Γ ρ ζ t| ≤ C₁ / (2 * (1 + Real.sqrt (-t))) := by
  intro ρ hρ
  unfold Phi
  rcases eq_or_lt_of_le hρ with h0 | hpos
  · subst h0
    simp only [hΓ0, zero_pow (by norm_num : (2:ℕ) ≠ 0), div_zero, abs_zero]
    exact div_nonneg hC₁ (by positivity)
  · have hp2 : 0 < ρ ^ 2 := pow_pos hpos 2
    have hΓ := h ρ hρ
    rw [abs_div, abs_of_pos hp2, div_le_iff₀ hp2]
    have heq : C₁ / (2 * (1 + Real.sqrt (-t))) * ρ ^ 2
        = C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by ring
    rw [heq]
    exact hΓ

/-! ## 打包：`prop:bound` 的积分步（条件版本） -/

/-- **`prop:bound` 的积分步**。设 `Γ = Γ(ρ,ζ,t)` 轴正则（`Γ(0,ζ,t) = 0`）、
在 ρ 方向可微且 `∂_ρΓ` 区间可积，并满足由 (H2) 得到的逐点界
`|∂_ρΓ| ≤ C₁ρ/R`；则 `|Φ| = |Γ|/ρ² ≤ C₁/(2(1+√-t))`，对一切 `ρ ≥ 0`、`ζ`、
`t ≤ 0`。

`t ≤ 0` 这个假设本身用不到（`Real.sqrt` 是全定义的），保留它是为了与论文的量词一致。 -/
theorem Phi_bound (Γ : ℝ → ℝ → ℝ → ℝ) (C₁ : ℝ)
    (hC₁ : 0 ≤ C₁)
    (hΓ0 : ∀ ζ t, Γ 0 ζ t = 0)
    (hdiff : ∀ ζ t, ∀ ρ, 0 ≤ ρ → DifferentiableAt ℝ (fun r => Γ r ζ t) ρ)
    (hint : ∀ ζ t, ∀ ρ, 0 ≤ ρ →
      IntervalIntegrable (deriv (fun r => Γ r ζ t)) volume 0 ρ)
    (hbound : ∀ ρ ζ t, 0 ≤ ρ → |deriv (fun r => Γ r ζ t) ρ| ≤ C₁ * ρ / R ρ ζ t) :
    ∀ ρ ζ t, 0 ≤ ρ → t ≤ 0 → |Phi Γ ρ ζ t| ≤ C₁ / (2 * (1 + Real.sqrt (-t))) := by
  intro ρ ζ t hρ _
  refine abs_Phi_le Γ C₁ ζ t hC₁ (hΓ0 ζ t) ?_ ρ hρ
  intro r hr
  exact abs_Gamma_le Γ C₁ ζ t r hC₁ hr (hΓ0 ζ t) (hdiff ζ t)
    (hint ζ t r hr) (fun s hs => hbound s ζ t hs.1)

/-! ## 轴上的值：`Φ` 的光滑延拓

(eq:Phi) 把 `Φ` 定义为光滑提升 `Φ=g(\lvert y\rvert^2,y_5,t)`，因此
`Φ(0,ζ,t)=g(0,ζ,t)=\lim_{ρ→0}Γ/ρ²`，**一般非零**。
而 Lean 的实数除法有 `x/0=0`，所以上面 `Phi Γ 0 ζ t = 0`——这与论文的值不同。
若只断言 `0 ≤ C`，就悄悄把一个非平凡的点换成了平凡真。

这里补上：引入连续延拓值 `Φ₀`，把轴正则写成它真正的内容——`Γ/ρ²` 在 `ρ→0⁺` 有极限。
于是结论覆盖 `ρ ≥ 0` 的全部，与 (eq:bound) 的量词一致。 -/

/-- `Φ` 的延拓：`ρ>0` 处取 `Γ/ρ²`，`ρ=0` 处取轴正则给出的极限值 `Φ₀(ζ,t)=g(0,ζ,t)`。 -/
def PhiExt (Γ : ℝ → ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ → ℝ) (ρ ζ t : ℝ) : ℝ :=
  if ρ = 0 then Φ₀ ζ t else Γ ρ ζ t / ρ ^ 2

lemma PhiExt_of_pos (Γ : ℝ → ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ → ℝ) {ρ : ℝ}
    (hρ : ρ ≠ 0) (ζ t : ℝ) : PhiExt Γ Φ₀ ρ ζ t = Phi Γ ρ ζ t := by
  unfold PhiExt Phi
  split_ifs with h
  · exact absurd h hρ
  · rfl

/-- **`prop:bound` 的积分步，覆盖 `ρ ≥ 0`（台账 A34）。**

除前面的假设外，再加一条轴正则的等价形式：`Γ(ρ,ζ,t)/ρ² → Φ₀(ζ,t)`（`ρ→0⁺`）。
轴上界由 `ρ>0` 的一致界取极限得到。 -/
theorem PhiExt_bound (Γ : ℝ → ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ → ℝ) (C₁ : ℝ)
    (hC₁ : 0 ≤ C₁)
    (hΓ0 : ∀ ζ t, Γ 0 ζ t = 0)
    (hdiff : ∀ ζ t, ∀ ρ, 0 ≤ ρ → DifferentiableAt ℝ (fun r => Γ r ζ t) ρ)
    (hint : ∀ ζ t, ∀ ρ, 0 ≤ ρ →
      IntervalIntegrable (deriv (fun r => Γ r ζ t)) volume 0 ρ)
    (hbound : ∀ ρ ζ t, 0 ≤ ρ → |deriv (fun r => Γ r ζ t) ρ| ≤ C₁ * ρ / R ρ ζ t)
    (hΦ₀ : ∀ ζ t, Tendsto (fun ρ => Γ ρ ζ t / ρ ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Φ₀ ζ t))) :
    ∀ ρ ζ t, 0 ≤ ρ → t ≤ 0 → |PhiExt Γ Φ₀ ρ ζ t| ≤ C₁ / (2 * (1 + Real.sqrt (-t))) := by
  intro ρ ζ t hρ ht
  by_cases h0 : ρ = 0
  · -- 轴上：由 ρ→0⁺ 的一致界取极限
    subst h0
    have hval : PhiExt Γ Φ₀ 0 ζ t = Φ₀ ζ t := by
      unfold PhiExt
      split_ifs with h
      · rfl
      · exact absurd rfl h
    rw [hval]
    have htend : Tendsto (fun ρ : ℝ => |Γ ρ ζ t / ρ ^ 2|) (nhdsWithin 0 (Set.Ioi 0))
        (nhds |Φ₀ ζ t|) := (hΦ₀ ζ t).abs
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : (0:ℝ) < r)
    exact Phi_bound Γ C₁ hC₁ hΓ0 hdiff hint hbound r ζ t hr.le ht
  · -- ρ>0：回到 Phi_bound
    rw [PhiExt_of_pos Γ Φ₀ h0 ζ t]
    exact Phi_bound Γ C₁ hC₁ hΓ0 hdiff hint hbound ρ ζ t hρ ht

/-- A34（覆盖 `ρ ≥ 0`）的推论：`∀ε>0 ∃T ∀t≤T ∀ρ≥0 ∀ζ, |Φ| ≤ ε`。 -/
theorem PhiExt_bound_tendsto (Γ : ℝ → ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ → ℝ) (C₁ : ℝ)
    (hC₁ : 0 ≤ C₁)
    (hΓ0 : ∀ ζ t, Γ 0 ζ t = 0)
    (hdiff : ∀ ζ t, ∀ ρ, 0 ≤ ρ → DifferentiableAt ℝ (fun r => Γ r ζ t) ρ)
    (hint : ∀ ζ t, ∀ ρ, 0 ≤ ρ →
      IntervalIntegrable (deriv (fun r => Γ r ζ t)) volume 0 ρ)
    (hbound : ∀ ρ ζ t, 0 ≤ ρ → |deriv (fun r => Γ r ζ t) ρ| ≤ C₁ * ρ / R ρ ζ t)
    (hΦ₀ : ∀ ζ t, Tendsto (fun ρ => Γ ρ ζ t / ρ ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Φ₀ ζ t))) :
    ∀ ε > 0, ∃ T, ∀ t ≤ T, ∀ ρ ζ, 0 ≤ ρ → |PhiExt Γ Φ₀ ρ ζ t| ≤ ε := by
  intro ε hε
  have hdecay : Tendsto (fun t : ℝ => C₁ / (2 * (1 + Real.sqrt (-t)))) atBot (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => -t) atBot atTop := tendsto_neg_atBot_atTop
    have h2 : Tendsto (fun t : ℝ => Real.sqrt (-t)) atBot atTop :=
      Real.tendsto_sqrt_atTop.comp h1
    have h3 : Tendsto (fun t : ℝ => 1 + Real.sqrt (-t)) atBot atTop :=
      tendsto_atTop_add_const_left atBot (1 : ℝ) h2
    have h4 : Tendsto (fun t : ℝ => (1 + Real.sqrt (-t))⁻¹) atBot (nhds 0) :=
      tendsto_inv_atTop_zero.comp h3
    have h5 := h4.const_mul (C₁ / 2)
    have hEq : (fun t : ℝ => C₁ / (2 * (1 + Real.sqrt (-t))))
        = (fun t : ℝ => (C₁ / 2) * (1 + Real.sqrt (-t))⁻¹) := by
      funext t
      have hpos : (1 + Real.sqrt (-t)) ≠ 0 := ne_of_gt (one_add_sqrt_pos t)
      field_simp
    rw [hEq]
    simpa using h5
  have hev : ∀ᶠ t : ℝ in atBot, C₁ / (2 * (1 + Real.sqrt (-t))) ≤ ε :=
    hdecay.eventually (eventually_le_nhds hε)
  obtain ⟨T, hT⟩ := eventually_atBot.1 hev
  refine ⟨min T 0, ?_⟩
  intro t ht ρ ζ hρ
  have htT : t ≤ T := le_trans ht (min_le_left _ _)
  have ht0 : t ≤ 0 := le_trans ht (min_le_right _ _)
  exact le_trans
    (PhiExt_bound Γ Φ₀ C₁ hC₁ hΓ0 hdiff hint hbound hΦ₀ ρ ζ t hρ ht0) (hT t htT)

end

end Liouville
