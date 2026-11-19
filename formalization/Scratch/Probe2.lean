import Mathlib

/-!
# Probe 2 : `cor:tradeoff` (paperA/mainA.tex, l. 511)

Target (verbatim from the paper):

  For `h = ρ^a`, `a > 0`,
    Δ_μ ρ^a = a(a-2) ρ^{a-2},      b · ∇ρ^a = a ρ^{a-1} b^ρ,
  so the hypothesis of `thm:weights2` is `b^ρ ≥ ν(a-2)/ρ`.  The requirement of
  uniform backward decay `sup_{ρ>0} ρ^2/ρ^a < ∞` is equivalent to `a ≥ 2`; the
  requirement that the threshold be weaker than `b^ρ ≥ 0`, i.e.
  `ν(a-2)/ρ ≤ 0`, is equivalent to `a ≤ 2`.  Both hold only at `a = 2`.
  Equivalently `h'' ≤ h'/ρ` forces `h ≤ C ρ^2`, while uniform decay forces
  `h ≥ c ρ^2`.

Conventions (paperA l. 84 and l. 179):
  `Δ_μ := ∂_ρ² - ρ⁻¹ ∂_ρ + ∂_ζ²`  (sign of the first-order term is MINUS),
  `b · ∇h := b^ρ ∂_ρ h + b^ζ ∂_ζ h`.
-/

namespace Liouville.Probe

open Real Filter

open scoped Topology

/-- `Δ_μ := ∂_ρ² - ρ⁻¹ ∂_ρ + ∂_ζ²`, on `ρ > 0` (paperA, l. 84).
Partial derivatives are expressed with `deriv`; the first-order term has the
sign `-ρ⁻¹` exactly as in the paper. -/
noncomputable def DeltaMu (f : ℝ → ℝ → ℝ) (ρ ζ : ℝ) : ℝ :=
  deriv (fun ρ' => deriv (fun ρ'' => f ρ'' ζ) ρ') ρ
    - ρ⁻¹ * deriv (fun ρ' => f ρ' ζ) ρ
    + deriv (fun ζ' => deriv (fun ζ'' => f ρ ζ'') ζ') ζ

/-- `b · ∇h := b^ρ ∂_ρ h + b^ζ ∂_ζ h` (paperA, l. 179). -/
noncomputable def bDotGrad (bRho bZeta : ℝ → ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (ρ ζ : ℝ) : ℝ :=
  bRho ρ ζ * deriv (fun ρ' => h ρ' ζ) ρ + bZeta ρ ζ * deriv (fun ζ' => h ρ ζ') ζ

/-- The radial power weight `h = ρ^a` (independent of `ζ`). -/
noncomputable def RadialPowerWeight (a : ℝ) : ℝ → ℝ → ℝ := fun ρ _ => ρ ^ a

/-! ## Piece 2 : `b · ∇ρ^a = a ρ^{a-1} b^ρ` -/

theorem deriv_radialPowerWeight_rho (a ρ ζ : ℝ) :
    deriv (fun ρ' => RadialPowerWeight a ρ' ζ) ρ = a * ρ ^ (a - 1) := by
  simp only [RadialPowerWeight, Real.deriv_rpow_const]

theorem deriv_radialPowerWeight_zeta (a ρ ζ : ℝ) :
    deriv (fun ζ' => RadialPowerWeight a ρ ζ') ζ = 0 := by
  simp [RadialPowerWeight]

theorem bDotGrad_radialPowerWeight (bRho bZeta : ℝ → ℝ → ℝ) (a ρ ζ : ℝ) :
    bDotGrad bRho bZeta (RadialPowerWeight a) ρ ζ
      = a * ρ ^ (a - 1) * bRho ρ ζ := by
  unfold bDotGrad
  rw [deriv_radialPowerWeight_rho, deriv_radialPowerWeight_zeta]
  ring

/-! ## Piece 1 : `Δ_μ ρ^a = a(a-2) ρ^{a-2}` -/

theorem deriv2_radialPowerWeight (a ρ ζ : ℝ) :
    deriv (fun ρ' => deriv (fun ρ'' => RadialPowerWeight a ρ'' ζ) ρ') ρ
      = a * (a - 1) * ρ ^ (a - 2) := by
  rw [show (fun ρ' => deriv (fun ρ'' => RadialPowerWeight a ρ'' ζ) ρ')
        = fun ρ' => a * ρ' ^ (a - 1) from by
      funext ρ'; exact deriv_radialPowerWeight_rho a ρ' ζ]
  rw [deriv_const_mul_field, Real.deriv_rpow_const]
  have h : a - 1 - 1 = a - 2 := by ring
  rw [h]
  ring

theorem DeltaMu_radialPowerWeight (a : ℝ) {ρ ζ : ℝ} (hρ : 0 < ρ) :
    DeltaMu (RadialPowerWeight a) ρ ζ = a * (a - 2) * ρ ^ (a - 2) := by
  unfold DeltaMu
  have hζ2 : deriv (fun ζ' => deriv (fun ζ'' => RadialPowerWeight a ρ ζ'') ζ') ζ = 0 := by
    simp [RadialPowerWeight]
  rw [hζ2, deriv2_radialPowerWeight, deriv_radialPowerWeight_rho]
  -- goal: a * (a-1) * ρ^(a-2) - ρ⁻¹ * (a * ρ^(a-1)) + 0 = a * (a-2) * ρ^(a-2)
  have hsplit : ρ ^ (a - 1) = ρ ^ (a - 2) * ρ := by
    have h : a - 1 = (a - 2) + 1 := by ring
    rw [h, Real.rpow_add hρ, Real.rpow_one]
  rw [hsplit]
  field_simp
  ring


/-! ## Piece 4 : the threshold is `b^ρ ≥ ν(a-2)/ρ` -/

/-- For `a > 0`, `ν > 0` and `ρ > 0` the weight hypothesis
`ν Δ_μ ρ^a ≤ b · ∇ρ^a` of `thm:weights2` is *equivalent* to
`ν (a-2)/ρ ≤ b^ρ`.  This is the algebra in the first sentence of
`cor:tradeoff`; no analysis. -/
theorem threshold_iff (ν a : ℝ) (hν : 0 < ν) (ha : 0 < a) {ρ : ℝ} (hρ : 0 < ρ)
    (bRho bZeta : ℝ → ℝ → ℝ) (ζ : ℝ) :
    ν * DeltaMu (RadialPowerWeight a) ρ ζ
        ≤ bDotGrad bRho bZeta (RadialPowerWeight a) ρ ζ
      ↔ ν * (a - 2) / ρ ≤ bRho ρ ζ := by
  rw [DeltaMu_radialPowerWeight a hρ, bDotGrad_radialPowerWeight]
  have hsplit : ρ ^ (a - 1) = ρ ^ (a - 2) * ρ := by
    have h : a - 1 = (a - 2) + 1 := by ring
    rw [h, Real.rpow_add hρ, Real.rpow_one]
  have hpos : 0 < a * ρ ^ (a - 1) := mul_pos ha (Real.rpow_pos_of_pos hρ _)
  have hrp : ρ ^ (a - 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hρ _)
  have key : ν * (a * (a - 2) * ρ ^ (a - 2))
      = (a * ρ ^ (a - 1)) * (ν * (a - 2) / ρ) := by
    rw [hsplit]
    field_simp
  rw [key, mul_le_mul_iff_of_pos_left hpos]

/-! ## Piece 3 : `sup_{ρ>0} ρ²/ρ^a < ∞`

The paper states the equivalence with `a ≥ 2`.  Machine-checked, the
equivalence **with `a = 2`** holds on `ρ ∈ (0,∞)`; `a ≥ 2` is only the correct
threshold on the tail `ρ ≥ 1` (the region `ρ < 1` makes `ρ^{2-a}` blow up for
`a > 2`).  Both versions are formalised below. -/

/-- `sup_{ρ>0} ρ^2/ρ^a < ∞`, written with `ρ^2/ρ^a = ρ^{2-a}`. -/
def DecaySupBdd (a : ℝ) : Prop :=
  BddAbove (Set.range fun ρ : { x : ℝ // 0 < x } => (ρ : ℝ) ^ (2 - a))

/-- The same supremum restricted to the tail `ρ ≥ 1`. -/
def DecaySupBddTail (a : ℝ) : Prop :=
  BddAbove ((fun ρ : ℝ => ρ ^ (2 - a)) '' Set.Ici 1)

theorem decaySupBdd_two : DecaySupBdd 2 := by
  refine ⟨1, ?_⟩
  rintro y ⟨ρ, rfl⟩
  norm_num [Real.rpow_zero]

theorem not_decaySupBdd_of_lt {a : ℝ} (ha : a < 2) : ¬ DecaySupBdd a := by
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  have hs : 0 < 2 - a := by linarith
  have htend := tendsto_rpow_atTop hs
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp htend (M + 1)
  have hρpos : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hρge : B ≤ max B 1 := le_max_left B 1
  have hbig : M + 1 ≤ (max B 1 : ℝ) ^ (2 - a) := hB (max B 1) hρge
  have hsmall : (⟨max B 1, hρpos⟩ : { x : ℝ // 0 < x }) ^ (2 - a) ≤ M :=
    hM ⟨⟨max B 1, hρpos⟩, rfl⟩
  have : (max B 1 : ℝ) ^ (2 - a) ≤ M := hsmall
  linarith

theorem not_decaySupBdd_of_gt {a : ℝ} (ha : 2 < a) : ¬ DecaySupBdd a := by
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  have hs : 2 - a < 0 := by linarith
  have htend := tendsto_rpow_neg_nhdsGT_zero hs
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), M + 1 ≤ x ^ (2 - a) :=
    Filter.tendsto_atTop.mp htend (M + 1)
  rw [(nhdsGT_basis (0 : ℝ)).eventually_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have hxmem : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨by linarith, by linarith⟩
  have hP : M + 1 ≤ (ε / 2) ^ (2 - a) := hball hxmem
  have hxpos : 0 < ε / 2 := by linarith
  have hcontra : (⟨ε / 2, hxpos⟩ : { x : ℝ // 0 < x }) ^ (2 - a) ≤ M :=
    hM ⟨⟨ε / 2, hxpos⟩, rfl⟩
  have : (ε / 2 : ℝ) ^ (2 - a) ≤ M := hcontra
  linarith

/-- Correct form of the "uniform backward decay" half of `cor:tradeoff`. -/
theorem decaySupBdd_iff (a : ℝ) : DecaySupBdd a ↔ a = 2 := by
  constructor
  · intro h
    rcases lt_trichotomy a 2 with ha | ha | ha
    · exact absurd h (not_decaySupBdd_of_lt ha)
    · exact ha
    · exact absurd h (not_decaySupBdd_of_gt ha)
  · rintro rfl; exact decaySupBdd_two

/-- The tail version: on `ρ ≥ 1` the paper's `a ≥ 2` is correct. -/
theorem decaySupBddTail_iff (a : ℝ) : DecaySupBddTail a ↔ 2 ≤ a := by
  constructor
  · intro hbdd
    by_contra hlt
    push Not at hlt
    obtain ⟨M, hM⟩ := hbdd
    have hs : 0 < 2 - a := by linarith
    have htend := tendsto_rpow_atTop hs
    obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp htend (M + 1)
    have hρ1 : (1 : ℝ) ≤ max B 1 := le_max_right B 1
    have hρge : B ≤ max B 1 := le_max_left B 1
    have hmem : max B 1 ∈ Set.Ici (1 : ℝ) := hρ1
    have hbig : M + 1 ≤ (max B 1 : ℝ) ^ (2 - a) := hB (max B 1) hρge
    have hsmall : (max B 1 : ℝ) ^ (2 - a) ≤ M := hM ⟨max B 1, hmem, rfl⟩
    linarith
  · intro ha
    refine ⟨1, ?_⟩
    rintro y ⟨ρ, hρ, rfl⟩
    exact Real.rpow_le_one_of_one_le_of_nonpos hρ (by linarith)

/-- The paper's `a ≥ 2` reading is **false** on `ρ ∈ (0,∞)`: e.g. at `a = 3`
the supremum is infinite although `3 ≥ 2`. -/
theorem paper_reading_false : ¬ (∀ a : ℝ, DecaySupBdd a ↔ 2 ≤ a) := by
  intro h
  have h3 : DecaySupBdd 3 := (h 3).mpr (by norm_num)
  have : (3 : ℝ) = 2 := (decaySupBdd_iff 3).mp h3
  norm_num at this

/-! ## Piece 5 : `h'' ≤ h'/ρ` ⇒ at most quadratic growth -/

/-- The literal statement "`h'' ≤ h'/ρ` forces `h ≤ C ρ²` **on all of
`(0,∞)`** is false: `h(ρ) = 1 - ρ²` satisfies `h'' = -2 = h'/ρ` and violates
`h ≤ C ρ²` as `ρ → 0⁺`. -/
theorem growth_claim_false_on_all_rho :
    ¬ ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → 1 - ρ ^ 2 ≤ C * ρ ^ 2 := by
  rintro ⟨C, hC⟩
  have hall : ∀ ρ : ℝ, 0 < ρ → 1 ≤ (C + 1) * ρ ^ 2 := by
    intro ρ hρ
    have := hC ρ hρ
    nlinarith
  rcases le_or_gt (C + 1) 0 with hle | hpos
  · have := hall 1 one_pos
    nlinarith
  · have hden : (0:ℝ) < C + 2 := by linarith
    have hq : (C + 1) * (1 / (2 * (C + 2))) ^ 2 ≤ 1 / 4 := by
      have heq : (C + 1) * (1 / (2 * (C + 2))) ^ 2 = (C + 1) / (4 * (C + 2) ^ 2) := by
        field_simp
        ring
      rw [heq, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (C + 1), hden]
    have h1 := hall (1 / (2 * (C + 2))) (by positivity)
    linarith

/-- Corrected form of the last sentence of `cor:tradeoff`, and the only one
that survives: `h'' ≤ h'/ρ` gives at most quadratic growth **at infinity**
(`ρ ≥ 1`).  The paper writes `h ≤ C ρ²` on all of `ρ > 0`, which is refuted by
`growth_claim_false_on_all_rho`. -/
theorem radial_growth_at_infinity (h : ℝ → ℝ)
    (hd : DifferentiableOn ℝ h (Set.Ioi 0))
    (hd2 : DifferentiableOn ℝ (deriv h) (Set.Ioi 0))
    (hineq : ∀ ρ ∈ Set.Ioi 0, deriv (deriv h) ρ ≤ deriv h ρ / ρ) :
    ∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → h ρ ≤ C * ρ ^ 2 := by
  -- Step 1: `q ρ = h'ρ / ρ` is antitone on `(0,∞)`.
  have hqanti : AntitoneOn (fun ρ : ℝ => deriv h ρ / ρ) (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx
      have hx0 : 0 < x := hx
      have hxd : DifferentiableAt ℝ (deriv h) x := hd2.differentiableAt (isOpen_Ioi.mem_nhds hx0)
      exact (hxd.continuousAt.div continuousAt_id (ne_of_gt hx0)).continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := interior_subset hx
      have hxd : DifferentiableAt ℝ (deriv h) x := hd2.differentiableAt (isOpen_Ioi.mem_nhds hx0)
      exact (hxd.div differentiableAt_id (ne_of_gt hx0)).differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := interior_subset hx
      have hxd : HasDerivAt (deriv h) (deriv (deriv h) x) x :=
        (hd2.differentiableAt (isOpen_Ioi.mem_nhds hx0)).hasDerivAt
      have hq : HasDerivAt (fun ρ => deriv h ρ / ρ)
          ((deriv (deriv h) x * x - deriv h x * 1) / x ^ 2) x :=
        hxd.div (hasDerivAt_id x) (ne_of_gt hx0)
      rw [hq.deriv]
      refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
      have := (le_div_iff₀ hx0).mp (hineq x (by simpa using hx0))
      linarith
  -- Step 2: for `ρ ≥ 1`, `h'ρ ≤ h'1 · ρ`.
  have hpbound : ∀ ρ : ℝ, 1 ≤ ρ → deriv h ρ ≤ deriv h 1 * ρ := by
    intro ρ hρ
    have hρ' : ρ ∈ Set.Ioi 0 := lt_of_lt_of_le one_pos hρ
    have hq := hqanti (by simpa using one_pos : (1:ℝ) ∈ Set.Ioi 0) hρ' hρ
    have hq1 : deriv h ρ / ρ ≤ deriv h 1 := by simpa using hq
    have := (div_le_iff₀ (lt_of_lt_of_le one_pos hρ)).mp hq1
    simpa using this
  -- Step 3: `G t = h t - h'1 · t²/2` is antitone on `[1,∞)`.
  let G : ℝ → ℝ := fun t => h t - deriv h 1 * t ^ 2 / 2
  have hGanti : AntitoneOn G (Set.Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
      have hxd : DifferentiableAt ℝ h x := hd.differentiableAt (isOpen_Ioi.mem_nhds hxpos)
      exact (hxd.continuousAt.sub (by fun_prop :
        ContinuousAt (fun t : ℝ => deriv h 1 * t ^ 2 / 2) x)).continuousWithinAt
    · intro x hx
      have hx1 : 1 ≤ x := interior_subset hx
      have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
      have hxd : DifferentiableAt ℝ h x := hd.differentiableAt (isOpen_Ioi.mem_nhds hxpos)
      exact (hxd.sub (by fun_prop :
        DifferentiableAt ℝ (fun t : ℝ => deriv h 1 * t ^ 2 / 2) x)).differentiableWithinAt
    · intro x hx
      have hx1 : 1 ≤ x := interior_subset hx
      have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
      have hxd : HasDerivAt h (deriv h x) x :=
        (hd.differentiableAt (isOpen_Ioi.mem_nhds hxpos)).hasDerivAt
      have hq : HasDerivAt (fun t : ℝ => deriv h 1 * t ^ 2 / 2) (deriv h 1 * x) x := by
        have h0 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have h1 : HasDerivAt (fun t : ℝ => deriv h 1 * t ^ 2) (deriv h 1 * (2 * x)) x :=
          h0.const_mul (deriv h 1)
        have h2 : HasDerivAt (fun t : ℝ => deriv h 1 * t ^ 2 / 2)
            (deriv h 1 * (2 * x) / 2) x := h1.div_const 2
        have h3 : deriv h 1 * (2 * x) / 2 = deriv h 1 * x := by ring
        rw [h3] at h2; exact h2
      have hG' : HasDerivAt G (deriv h x - deriv h 1 * x) x := hxd.sub hq
      rw [hG'.deriv]
      have := hpbound x hx1
      linarith
  -- Step 4: conclude.
  refine ⟨|h 1| + |deriv h 1|, fun ρ hρ => ?_⟩
  have hGle : G ρ ≤ G 1 := hGanti (by simpa using le_refl (1:ℝ) : (1:ℝ) ∈ Set.Ici 1) (by simpa using hρ) hρ
  have hexp : h ρ ≤ h 1 + deriv h 1 * (ρ ^ 2 - 1) / 2 := by
    have : h ρ - deriv h 1 * ρ ^ 2 / 2 ≤ h 1 - deriv h 1 * 1 ^ 2 / 2 := hGle
    linarith
  have hsq : (1:ℝ) ≤ ρ ^ 2 := by nlinarith
  have hA : |h 1| ≤ |h 1| * ρ ^ 2 := by nlinarith [abs_nonneg (h 1)]
  have hB : deriv h 1 * (ρ ^ 2 - 1) / 2 ≤ |deriv h 1| * ρ ^ 2 := by
    have hmul : deriv h 1 * (ρ ^ 2 - 1) / 2 ≤ |deriv h 1| * (ρ ^ 2 - 1) / 2 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (le_abs_self _) (by nlinarith)
      · norm_num
    have hle2 : |deriv h 1| * (ρ ^ 2 - 1) / 2 ≤ |deriv h 1| * ρ ^ 2 := by
      nlinarith [abs_nonneg (deriv h 1)]
    linarith
  have hC : h 1 ≤ |h 1| := le_abs_self _
  nlinarith


/-! ## Piece 4b : `ν(a-2)/ρ ≤ 0` for all `ρ > 0` ⇔ `a ≤ 2` -/

theorem threshold_le_zero_iff {ν a : ℝ} (hν : 0 < ν) :
    (∀ ρ : ℝ, 0 < ρ → ν * (a - 2) / ρ ≤ 0) ↔ a ≤ 2 := by
  constructor
  · intro h
    have := h 1 one_pos
    have : ν * (a - 2) ≤ 0 := by simpa using this
    nlinarith
  · intro ha ρ hρ
    have h1 : ν * (a - 2) ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hρ)

/-- The concluding sentence of `cor:tradeoff` ("both hold only at `a = 2`")
survives even though the two individual equivalences as printed do not. -/
theorem no_other_weight {ν a : ℝ} (ha : a ≠ 2) :
    ¬ (DecaySupBdd a ∧ ∀ ρ : ℝ, 0 < ρ → ν * (a - 2) / ρ ≤ 0) := by
  rintro ⟨hdec, -⟩
  exact ha ((decaySupBdd_iff a).mp hdec)

-- Sanity check: none of the proofs used `sorry`.
#print axioms Liouville.Probe.DeltaMu_radialPowerWeight
#print axioms Liouville.Probe.threshold_iff
#print axioms Liouville.Probe.decaySupBdd_iff
#print axioms Liouville.Probe.radial_growth_at_infinity 
end Liouville.Probe
