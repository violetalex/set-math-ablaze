/-
Probe 1 — `prop:bound` (paper A, paperA/mainA.tex:354)

Uniform backward bound for the lifted swirl `Φ = Γ/ρ²`:

  under (H1)--(H3) and axis regularity (eq:axis), with `R = 1 + |x| + √(-t)` (eq:R),
    |Φ(t,ρ,ζ)| ≤ C₁ / (2 (1 + √(-t)))   for all ρ, ζ, t ≤ 0,
  in particular ‖Φ(t)‖∞ → 0 as t → -∞.

SCOPE OF THIS PROBE (see `statement_locked` in the report):
this file formalises the *meridional-profile reduction* that the paper's proof
actually performs.  Namely, the whole content is the one-dimensional estimate
in ρ

  |Γ(ρ)| ≤ ∫₀^ρ C₁ ρ'/R(ρ',t) dρ' ≤ C₁ ρ² / (2 (1+√(-t))),

from `Γ(0) = 0` (eq:axis) and `|∂_ρ Γ| ≤ C₁ ρ / R` (which is
`∂_ρ Γ = ρ ω^ζ`, eq:identities, plus (H2) `|ω^ζ| ≤ |ω| ≤ C₁/R`).

NOT formalised here (documented gap, not a silent weakening):
  * the derivation `∂_ρ Γ = ρ ω^ζ` from the *definition* of `ω` in eq:identities
    is formalised as the algebraic identity `ρ * omegaZeta Γ ρ = deriv Γ ρ`
    (`deriv_Gamma_eq`), but the passage `|ω^ζ| ≤ |ω| ≤ C₁/R` from (H2) on the
    full R³ vector field is taken as the hypothesis `hbound` below;
  * `‖Φ(t)‖∞ → 0` is formalised only for the *bound itself*
    (`bound_tendsto_zero`); identifying `‖Φ(t)‖∞` with a supremum over (ρ,ζ)
    and applying a squeeze is left as a gap (needs the `sSup` construction).

No `sorry` anywhere: every gap is a comment.
-/
import Mathlib

open Real Set Filter MeasureTheory
open scoped Interval

namespace Liouville.Probe

noncomputable section

/-! ## Definitions, coefficient-for-coefficient as in the paper -/

/-- eq:R — `R(x,t) = 1 + |x| + √(-t)`, written in the meridional variable
`ρ = |x_meridional|` (the θ-dependence drops out by axisymmetry). -/
def R (ρ t : ℝ) : ℝ := 1 + ρ + Real.sqrt (-t)

/-- eq:identities — `ω^ζ = (1/ρ) ∂_ρ (ρ u^θ) = Γ_ρ / ρ`. -/
def omegaZeta (Γ : ℝ → ℝ) (ρ : ℝ) : ℝ := deriv Γ ρ / ρ

/-- eq:Phi — the lifted variable `Φ = Γ / ρ²`. -/
def Phi (Γ : ℝ → ℝ) (ρ : ℝ) : ℝ := Γ ρ / ρ ^ 2

/-! ## Elementary facts about `R` -/

lemma R_ge (ρ t : ℝ) (hρ : 0 ≤ ρ) : 1 + Real.sqrt (-t) ≤ R ρ t := by
  unfold R; linarith

lemma R_pos (ρ t : ℝ) (hρ : 0 ≤ ρ) : 0 < R ρ t := by
  unfold R
  have := Real.sqrt_nonneg (-t)
  linarith

lemma R_zero (t : ℝ) : R 0 t = 1 + Real.sqrt (-t) := by
  unfold R; ring

lemma one_add_sqrt_pos (t : ℝ) : 0 < 1 + Real.sqrt (-t) := by
  have := Real.sqrt_nonneg (-t); linarith

/-! ## Step 1 (easy): `∂_ρ Γ = ρ ω^ζ` -/

/-- The identity `∂_ρ Γ = ρ ω^ζ` of eq:identities, at the level of the
definitions `omegaZeta = Γ_ρ/ρ` and `Γ = ρ u^θ`. -/
theorem deriv_Gamma_eq (Γ : ℝ → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) :
    ρ * omegaZeta Γ ρ = deriv Γ ρ := by
  unfold omegaZeta
  field_simp

/-! ## Step 2 (medium): the sharp integral estimate

If `Γ(0) = 0` and `|Γ' r| ≤ C₁ r / R(r,t)` on `[0,ρ]`, then
`|Γ ρ| ≤ C₁ ρ² / (2 (1+√(-t)))`, with the *exact* constant `1/2` of the paper
(no factor-2 loss: the pointwise bound `1/R ≤ 1/(1+√(-t))` is integrated,
not pulled out as a supremum). -/

theorem abs_Gamma_le
    (Γ : ℝ → ℝ) (C₁ t ρ : ℝ)
    (hC₁ : 0 ≤ C₁) (hρ : 0 ≤ ρ)
    (hΓ0 : Γ 0 = 0)
    (hdiff : ∀ x, 0 ≤ x → DifferentiableAt ℝ Γ x)
    (hint : IntervalIntegrable (deriv Γ) volume 0 ρ)
    (hbound : ∀ r ∈ Icc 0 ρ, |deriv Γ r| ≤ C₁ * r / R r t) :
    |Γ ρ| ≤ C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by
  -- Fundamental theorem of calculus: Γ ρ - Γ 0 = ∫₀^ρ Γ'
  have hdiff' : ∀ x ∈ uIcc 0 ρ, DifferentiableAt ℝ Γ x := by
    intro x hx
    rw [uIcc_of_le hρ] at hx
    exact hdiff x hx.1
  have hfund : ∫ r in (0)..ρ, deriv Γ r = Γ ρ - Γ 0 :=
    intervalIntegral.integral_deriv_eq_sub hdiff' hint
  -- The pointwise bound on the derivative, with the *constant* denominator.
  have hpt : ∀ r ∈ Ioc 0 ρ, ‖deriv Γ r‖ ≤ C₁ * r / (1 + Real.sqrt (-t)) := by
    intro r hr
    rw [Real.norm_eq_abs]
    have hr0 : 0 ≤ r := le_of_lt hr.1
    have hle := hbound r (Ioc_subset_Icc_self hr)
    have hRge : 1 + Real.sqrt (-t) ≤ R r t := R_ge r t hr0
    have hpos : 0 < 1 + Real.sqrt (-t) := one_add_sqrt_pos t
    have h1 : C₁ * r / R r t ≤ C₁ * r / (1 + Real.sqrt (-t)) :=
      div_le_div_of_nonneg_left (mul_nonneg hC₁ hr0) hpos hRge
    linarith
  -- Interval integrability of the comparison function.
  have hg : IntervalIntegrable (fun r => C₁ * r / (1 + Real.sqrt (-t))) volume 0 ρ := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- The integral bound `|∫ Γ'| ≤ ∫ C₁ r/(1+√(-t))`.
  have hmain : ‖∫ r in (0)..ρ, deriv Γ r‖ ≤
      ∫ r in (0)..ρ, C₁ * r / (1 + Real.sqrt (-t)) :=
    intervalIntegral.norm_integral_le_of_norm_le hρ (Filter.Eventually.of_forall hpt) hg
  -- Evaluate the comparison integral.
  have hInt : ∫ r in (0)..ρ, C₁ * r / (1 + Real.sqrt (-t)) =
      C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by
    have hfun : (fun r => C₁ * r / (1 + Real.sqrt (-t)))
        = (fun r => (C₁ / (1 + Real.sqrt (-t))) * r) := by
      funext r; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_id]
    norm_num
    field_simp
  -- Combine.
  calc |Γ ρ| = |∫ r in (0)..ρ, deriv Γ r| := by
        rw [hfund, hΓ0, sub_zero]
    _ = ‖∫ r in (0)..ρ, deriv Γ r‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ r in (0)..ρ, C₁ * r / (1 + Real.sqrt (-t)) := hmain
    _ = C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := hInt

/-! ## Step 3 (medium): divide by `ρ²` -/

/-- `prop:bound`, pointwise form: `|Φ(ρ)| = |Γ ρ|/ρ² ≤ C₁/(2(1+√(-t)))`.
At `ρ = 0` both `Γ(0) = 0` and Lean's `x/0 = 0` make the claim trivial. -/
theorem abs_Phi_le
    (Γ : ℝ → ℝ) (C₁ t : ℝ) (hC₁ : 0 ≤ C₁)
    (hΓ0 : Γ 0 = 0)
    (h : ∀ ρ, 0 ≤ ρ → |Γ ρ| ≤ C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t)))) :
    ∀ ρ, 0 ≤ ρ → |Phi Γ ρ| ≤ C₁ / (2 * (1 + Real.sqrt (-t))) := by
  intro ρ hρ
  unfold Phi
  rcases eq_or_lt_of_le hρ with h0 | hpos
  · -- ρ = 0
    subst h0
    simp only [hΓ0, zero_pow (by norm_num : (2:ℕ) ≠ 0), div_zero, abs_zero]
    exact div_nonneg hC₁ (by positivity)
  · -- ρ > 0
    have hp2 : 0 < ρ ^ 2 := pow_pos hpos 2
    have hΓ := h ρ hρ
    rw [abs_div, abs_of_pos hp2, div_le_iff₀ hp2]
    have heq : C₁ / (2 * (1 + Real.sqrt (-t))) * ρ ^ 2
        = C₁ * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by
      ring
    rw [heq]
    exact hΓ

/-! ## Step 4 (medium): the decay `‖Φ(t)‖_∞ → 0`

This formalises the decay of the *bound* `C₁/(2(1+√(-t)))` as `t → -∞`.
Identifying `‖Φ(t)‖_∞` with the supremum `sSup` over `(ρ,ζ)` and squeezing is
the remaining (unformalised) step; see the header. -/

/-- The bound of `eq:bound` decays to zero, hence any `‖Φ(t)‖_∞` squeezed
between `0` and this bound tends to `0` (the `sSup` identification is the gap). -/
theorem bound_tendsto_zero (C₁ : ℝ) :
    Tendsto (fun t : ℝ => C₁ / (2 * (1 + Real.sqrt (-t)))) atBot (nhds 0) := by
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

/-! ## The packaged statement of `prop:bound` (pointwise form)

This is the exact inequality `eq:bound` of the paper, for the meridional
profile, with the hypotheses of the paper's proof: `Γ(0,ζ,t) = 0` (axis
regularity), differentiability in ρ, interval-integrability of `Γ_ρ`, and the
pointwise derivative bound `|Γ_ρ| ≤ C₁ ρ/R` (from eq:identities + (H2)).
The hypothesis `t ≤ 0` is carried although the estimate itself never uses it
(Lean's `Real.sqrt` is total); it is kept so the statement matches the paper. -/

theorem prop_bound
    (Γ : ℝ → ℝ) (C₁ t : ℝ)
    (hC₁ : 0 ≤ C₁) (ht : t ≤ 0)
    (hΓ0 : Γ 0 = 0)
    (hdiff : ∀ x, 0 ≤ x → DifferentiableAt ℝ Γ x)
    (hint : ∀ ρ, 0 ≤ ρ → IntervalIntegrable (deriv Γ) volume 0 ρ)
    (hbound : ∀ r, 0 ≤ r → |deriv Γ r| ≤ C₁ * r / R r t) :
    ∀ ρ, 0 ≤ ρ → |Phi Γ ρ| ≤ C₁ / (2 * (1 + Real.sqrt (-t))) := by
  have _ := ht
  refine abs_Phi_le Γ C₁ t hC₁ hΓ0 ?_
  intro ρ hρ
  exact abs_Gamma_le Γ C₁ t ρ hC₁ hρ hΓ0 hdiff (hint ρ hρ)
    (fun r hr => hbound r hr.1)

end

end Liouville.Probe
