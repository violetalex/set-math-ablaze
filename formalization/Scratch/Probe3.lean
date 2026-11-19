import Mathlib

/-!
# Probe 3 — `prop:timedep` (time-dependent weights of additive type give nothing new)

Source: `paperA/mainA.tex`, `\label{prop:timedep}` (line 615).

Paper statement, verbatim (reduced `(ρ,ζ,t)` coordinates, `ρ>0`):

> Let `f = f(ρ,ζ,t)` be SO(4)-invariant and `h = ρ² e^{f(t,x)}`, `w = Γ/h`.
> Then at every critical point of `w`,
>   `∂_t w = ν Δ_μ w + G w`,
>   `G = ν(Δ_5 f + |∇_5 f|²) − b·∇_5 f − (2 b^ρ)/ρ − ∂_t f`,
> so the amplitude is non-increasing only if `G ≤ 0`, i.e. `∂_t f ≥ R` with
>   `R = ν(Δ_5 f + |∇_5 f|²) − b·∇_5 f − 2 b^ρ/ρ`.
> With `f = ψ(x) + c(t)` this reads `c'(t) ≥ sup_x R(x)`; backward decay of
> `w = Φ e^{-f}` forces `c' ≤ 0`; hence `sup_x R ≤ 0`, which is exactly `(⋆)`.

Operators (paper eq. (2.4), prop:lift):
  `Δ_μ := ∂_ρ² − ρ⁻¹ ∂_ρ + ∂_ζ²`  (sign is MINUS, as in the paper)
  `Δ_5 := ∂_ρ² + 3ρ⁻¹ ∂_ρ + ∂_ζ²`  (Euclidean Laplacian of ℝ⁵ on SO(4)-invariants)
  `b·∇ = b^ρ∂_ρ + b^ζ∂_ζ`  (agrees with `b·∇_5` on invariants)

WHAT IS DONE HERE (all without `sorry`, without new axioms):
  * the operators, the transport equation, critical points, `R`, `G`;
  * product rule for `Δ_μ` (built from scratch: Mathlib has no Laplacian product rule);
  * the lift identity `Δ_μ(ρ²A) = ρ²Δ_5 A` (paper `eq:liftidentity`);
  * `Δ_5(e^f) = e^f(Δ_5f + |∇5f|²)` and `b·∇(ρ²e^f) = e^f(2ρb^ρ + ρ² b·∇5f)`;
  * THE MAIN IDENTITY `∂_t w = νΔ_μ w + G w` at a critical point;
  * `G ≤ 0 ↔ ∂_t f ≥ R`, and the additive-family form `G = R_ψ − c'`.

WHAT IS *NOT* DONE — see the `GAP:` comments at the end of the file:
  * the sup step `c'(t) ≥ sup_x R(x)` and the conclusion `sup_x R ≤ 0`;
  * the analytic input "backward decay of `w = Φe^{-f}` forces `c' ≤ 0`".
  Neither is a derivative identity: both need the global/Feynman--Kac layer of
  `thm:star2`, which is outside this probe's scope.
-/

noncomputable section
open Real

namespace Liouville.Probe

/-! ## Partial derivatives of `F : ℝ → ℝ → ℝ → ℝ` (arguments `t, ρ, ζ`) -/

/-- `∂_t F`. -/
def Dt (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ := deriv (fun s => F s r z) t

/-- `∂_ρ F`. -/
def Dr (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ := deriv (fun p => F t p z) r

/-- `∂_ζ F`. -/
def Dz (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ := deriv (fun q => F t r q) z

/-- `∂_ρ² F`. -/
def Drr (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ := deriv (fun p => Dr F t p z) r

/-- `∂_ζ² F`. -/
def Dzz (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ := deriv (fun q => Dz F t r q) z

/-- `Δ_μ F = ∂_ρ²F − ρ⁻¹∂_ρF + ∂_ζ²F` (paper eq. (2.4); the sign is `−`). -/
def DeltaMu (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ :=
  Drr F t r z - (1 / r) * Dr F t r z + Dzz F t r z

/-- `Δ_5 F = ∂_ρ²F + 3ρ⁻¹∂_ρF + ∂_ζ²F` (Euclidean Laplacian of ℝ⁵). -/
def Delta5 (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ :=
  Drr F t r z + (3 / r) * Dr F t r z + Dzz F t r z

/-- `|∇_5 F|² = (∂_ρF)² + (∂_ζF)²` for SO(4)-invariant `F`. -/
def grad5Sq (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ :=
  (Dr F t r z) ^ 2 + (Dz F t r z) ^ 2

/-- The meridional velocity `b = (b^ρ, b^ζ)` as a pair-valued function of `(t,ρ,ζ)`. -/
abbrev Meridional := ℝ → ℝ → ℝ → ℝ × ℝ

/-- `b·∇ F = b^ρ ∂_ρF + b^ζ ∂_ζF` (on SO(4)-invariants this is `b·∇_5`). -/
def bDotGrad (b : Meridional) (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ :=
  (b t r z).1 * Dr F t r z + (b t r z).2 * Dz F t r z

/-- `V_0 = div_5 b = 2 b^ρ / ρ`. -/
def V0 (b : Meridional) (t r z : ℝ) : ℝ := 2 * (b t r z).1 / r

/-- Critical point of `w` in the spatial variables (`∂_ρw = ∂_ζw = 0`). -/
def CriticalPoint (w : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : Prop :=
  Dr w t r z = 0 ∧ Dz w t r z = 0

/-- The swirl transport equation `∂_tΓ + b·∇Γ = ν Δ_μ Γ` (paper, before eq. (2.5)). -/
def TransportEq (ν : ℝ) (b : Meridional) (Γ : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ t r z, Dt Γ t r z + bDotGrad b Γ t r z = ν * DeltaMu Γ t r z

/-- `R = ν(Δ_5f + |∇_5f|²) − b·∇_5f − 2b^ρ/ρ` (paper `prop:timedep`). -/
def R (ν : ℝ) (b : Meridional) (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ :=
  ν * (Delta5 f t r z + grad5Sq f t r z) - bDotGrad b f t r z - V0 b t r z

/-- `G = R − ∂_t f` (paper `eq:G`). -/
def G (ν : ℝ) (b : Meridional) (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) : ℝ :=
  R ν b f t r z - Dt f t r z

/-- The weight `h = ρ² e^{f(t,x)}` of the paper. -/
def wgt (f : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun t r z => r ^ 2 * Real.exp (f t r z)

/-- `ρ²` seen as a function of `(t,ρ,ζ)`. -/
def rhoSq : ℝ → ℝ → ℝ → ℝ := fun _ r _ => r ^ 2

/-! ## Smoothness package

The paper's data are `C²` (indeed smooth) `SO(4)`-invariants.  We record exactly the
separate differentiability facts that the derivative computations consume:
`hrr`/`hzz` say the first partials are again differentiable, which is what the
second-order product rules need.  No mixed `∂_ρ∂_ζ` is required: both `Δ_μ`,
`Δ_5` and the drift term are diagonal in `(ρ,ζ)`. -/

/-- Separate `C²` regularity of `F` in each variable. -/
structure Smooth (F : ℝ → ℝ → ℝ → ℝ) : Prop where
  ht : ∀ t r z, DifferentiableAt ℝ (fun s => F s r z) t
  hr : ∀ t r z, DifferentiableAt ℝ (fun p => F t p z) r
  hz : ∀ t r z, DifferentiableAt ℝ (fun q => F t r q) z
  hrr : ∀ t r z, DifferentiableAt ℝ (fun p => Dr F t p z) r
  hzz : ∀ t r z, DifferentiableAt ℝ (fun q => Dz F t r q) z

variable {F G' : ℝ → ℝ → ℝ → ℝ}

/-! ## Product rules (built from scratch; Mathlib has no Laplacian product rule) -/

lemma Dt_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    Dt (fun t r z => F t r z * G' t r z) t r z
      = Dt F t r z * G' t r z + F t r z * Dt G' t r z := by
  simp only [Dt]
  change deriv ((fun s => F s r z) * (fun s => G' s r z)) t
      = deriv (fun s => F s r z) t * G' t r z + F t r z * deriv (fun s => G' s r z) t
  rw [deriv_mul (hF.ht t r z) (hG.ht t r z)]

lemma Dr_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    Dr (fun t r z => F t r z * G' t r z) t r z
      = Dr F t r z * G' t r z + F t r z * Dr G' t r z := by
  simp only [Dr]
  change deriv ((fun p => F t p z) * (fun p => G' t p z)) r
      = deriv (fun p => F t p z) r * G' t r z + F t r z * deriv (fun p => G' t p z) r
  rw [deriv_mul (hF.hr t r z) (hG.hr t r z)]

lemma Dz_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    Dz (fun t r z => F t r z * G' t r z) t r z
      = Dz F t r z * G' t r z + F t r z * Dz G' t r z := by
  simp only [Dz]
  change deriv ((fun q => F t r q) * (fun q => G' t r q)) z
      = deriv (fun q => F t r q) z * G' t r z + F t r z * deriv (fun q => G' t r q) z
  rw [deriv_mul (hF.hz t r z) (hG.hz t r z)]

lemma Drr_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    Drr (fun t r z => F t r z * G' t r z) t r z
      = Drr F t r z * G' t r z + 2 * Dr F t r z * Dr G' t r z
        + F t r z * Drr G' t r z := by
  simp only [Drr]
  have hfun : (fun p => Dr (fun t r z => F t r z * G' t r z) t p z)
      = fun p => Dr F t p z * G' t p z + F t p z * Dr G' t p z := by
    funext p; exact Dr_mul hF hG t p z
  rw [hfun]
  have h1 : DifferentiableAt ℝ (fun p => Dr F t p z * G' t p z) r :=
    (hF.hrr t r z).mul (hG.hr t r z)
  have h2 : DifferentiableAt ℝ (fun p => F t p z * Dr G' t p z) r :=
    (hF.hr t r z).mul (hG.hrr t r z)
  change deriv ((fun p => Dr F t p z * G' t p z) + fun p => F t p z * Dr G' t p z) r = _
  rw [deriv_add h1 h2]
  change deriv ((fun p => Dr F t p z) * (fun p => G' t p z)) r
      + deriv ((fun p => F t p z) * (fun p => Dr G' t p z)) r = _
  rw [deriv_mul (hF.hrr t r z) (hG.hr t r z),
      deriv_mul (hF.hr t r z) (hG.hrr t r z)]
  simp only [Dr]
  ring

lemma Dzz_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    Dzz (fun t r z => F t r z * G' t r z) t r z
      = Dzz F t r z * G' t r z + 2 * Dz F t r z * Dz G' t r z
        + F t r z * Dzz G' t r z := by
  simp only [Dzz]
  have hfun : (fun q => Dz (fun t r z => F t r z * G' t r z) t r q)
      = fun q => Dz F t r q * G' t r q + F t r q * Dz G' t r q := by
    funext q; exact Dz_mul hF hG t r q
  rw [hfun]
  have h1 : DifferentiableAt ℝ (fun q => Dz F t r q * G' t r q) z :=
    (hF.hzz t r z).mul (hG.hz t r z)
  have h2 : DifferentiableAt ℝ (fun q => F t r q * Dz G' t r q) z :=
    (hF.hz t r z).mul (hG.hzz t r z)
  change deriv ((fun q => Dz F t r q * G' t r q) + fun q => F t r q * Dz G' t r q) z = _
  rw [deriv_add h1 h2]
  change deriv ((fun q => Dz F t r q) * (fun q => G' t r q)) z
      + deriv ((fun q => F t r q) * (fun q => Dz G' t r q)) z = _
  rw [deriv_mul (hF.hzz t r z) (hG.hz t r z),
      deriv_mul (hF.hz t r z) (hG.hzz t r z)]
  simp only [Dz]
  ring

/-- Product rule for `Δ_μ`: the cross terms are `2(∂_ρF ∂_ρG + ∂_ζF ∂_ζG)`. -/
lemma DeltaMu_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    DeltaMu (fun t r z => F t r z * G' t r z) t r z
      = DeltaMu F t r z * G' t r z + F t r z * DeltaMu G' t r z
        + 2 * (Dr F t r z * Dr G' t r z + Dz F t r z * Dz G' t r z) := by
  simp only [DeltaMu]
  rw [Drr_mul hF hG, Dr_mul hF hG, Dzz_mul hF hG]
  ring

/-! ## `ρ²`: the lift identity `Δ_μ(ρ²A) = ρ²Δ_5A` -/

lemma Dr_rhoSq (t r z : ℝ) : Dr rhoSq t r z = 2 * r := by
  simp only [Dr, rhoSq]
  rw [deriv_pow_field]
  norm_num

lemma Dz_rhoSq (t r z : ℝ) : Dz rhoSq t r z = 0 := by
  simp only [Dz, rhoSq, deriv_const]

lemma Drr_rhoSq (t r z : ℝ) : Drr rhoSq t r z = 2 := by
  simp only [Drr]
  have hfun : (fun p => Dr rhoSq t p z) = fun p => 2 * p := by
    funext p; exact Dr_rhoSq t p z
  rw [hfun]
  rw [show (fun p : ℝ => 2 * p) = (fun _ => (2:ℝ)) * (fun x => x) by rfl]
  rw [deriv_mul (differentiableAt_const _) differentiableAt_id]
  simp

lemma Dzz_rhoSq (t r z : ℝ) : Dzz rhoSq t r z = 0 := by
  simp only [Dzz]
  have hfun : (fun q => Dz rhoSq t r q) = fun q => 0 := by
    funext q; exact Dz_rhoSq t r q
  rw [hfun]
  simp

lemma smooth_rhoSq : Smooth rhoSq where
  ht := by intro t r z; exact differentiableAt_const _
  hr := by
    intro t r z
    exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ => p ^ 2) r)
  hz := by intro t r z; exact differentiableAt_const _
  hrr := by
    intro t r z
    have hfun : (fun p => Dr rhoSq t p z) = fun p => 2 * p := by
      funext p; exact Dr_rhoSq t p z
    rw [hfun]; fun_prop
  hzz := by
    intro t r z
    have hfun : (fun q => Dz rhoSq t r q) = fun q => 0 := by
      funext q; exact Dz_rhoSq t r q
    rw [hfun]; exact differentiableAt_const _

lemma DeltaMu_rhoSq (t r z : ℝ) (hr : r ≠ 0) : DeltaMu rhoSq t r z = 0 := by
  simp only [DeltaMu, Drr_rhoSq, Dr_rhoSq, Dzz_rhoSq]
  field_simp
  ring

/-- `Δ_μ = Δ_5 − (4/ρ)∂_ρ`. -/
lemma DeltaMu_eq (F : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) :
    DeltaMu F t r z = Delta5 F t r z - (4 / r) * Dr F t r z := by
  simp only [DeltaMu, Delta5]; ring

/-- Paper `eq:liftidentity`: `Δ_μ(ρ²A) = ρ² Δ_5 A`. -/
lemma DeltaMu_rhoSq_mul (hA : Smooth A) (t r z : ℝ) (hr : r ≠ 0) :
    DeltaMu (fun t r z => r ^ 2 * A t r z) t r z = r ^ 2 * Delta5 A t r z := by
  change DeltaMu (fun t r z => rhoSq t r z * A t r z) t r z
      = rhoSq t r z * Delta5 A t r z
  have h := DeltaMu_mul (F := rhoSq) (G' := A) smooth_rhoSq hA t r z
  rw [h, DeltaMu_rhoSq t r z hr, Dr_rhoSq, Dz_rhoSq]
  simp only [DeltaMu, Delta5, rhoSq]
  field_simp
  ring

/-! ## Exponential chain rules and `Δ_5(e^f)` -/

lemma Dr_exp (hf : Smooth f) (t r z : ℝ) :
    Dr (fun t r z => Real.exp (f t r z)) t r z
      = Real.exp (f t r z) * Dr f t r z := by
  simp only [Dr]
  change deriv (Real.exp ∘ (fun p => f t p z)) r
      = Real.exp (f t r z) * deriv (fun p => f t p z) r
  rw [deriv_comp r Real.differentiableAt_exp (hf.hr t r z), Real.deriv_exp]

lemma Dz_exp (hf : Smooth f) (t r z : ℝ) :
    Dz (fun t r z => Real.exp (f t r z)) t r z
      = Real.exp (f t r z) * Dz f t r z := by
  simp only [Dz]
  change deriv (Real.exp ∘ (fun q => f t r q)) z
      = Real.exp (f t r z) * deriv (fun q => f t r q) z
  rw [deriv_comp z Real.differentiableAt_exp (hf.hz t r z), Real.deriv_exp]

lemma Dt_exp (hf : Smooth f) (t r z : ℝ) :
    Dt (fun t r z => Real.exp (f t r z)) t r z
      = Real.exp (f t r z) * Dt f t r z := by
  simp only [Dt]
  change deriv (Real.exp ∘ (fun s => f s r z)) t
      = Real.exp (f t r z) * deriv (fun s => f s r z) t
  rw [deriv_comp t Real.differentiableAt_exp (hf.ht t r z), Real.deriv_exp]

lemma Drr_exp (hf : Smooth f) (t r z : ℝ) :
    Drr (fun t r z => Real.exp (f t r z)) t r z
      = Real.exp (f t r z) * (Drr f t r z + (Dr f t r z) ^ 2) := by
  simp only [Drr]
  have hfun : (fun p => Dr (fun t r z => Real.exp (f t r z)) t p z)
      = fun p => Real.exp (f t p z) * Dr f t p z := by
    funext p; exact Dr_exp hf t p z
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun p => Real.exp (f t p z)) r := (hf.hr t r z).exp
  have hd2 : DifferentiableAt ℝ (fun p => Dr f t p z) r := hf.hrr t r z
  change deriv ((fun p => Real.exp (f t p z)) * (fun p => Dr f t p z)) r = _
  rw [deriv_mul hd1 hd2]
  rw [show deriv (fun p => Real.exp (f t p z)) r = Real.exp (f t r z) * Dr f t r z
        from Dr_exp hf t r z]
  simp only [Dr]
  ring

lemma Dzz_exp (hf : Smooth f) (t r z : ℝ) :
    Dzz (fun t r z => Real.exp (f t r z)) t r z
      = Real.exp (f t r z) * (Dzz f t r z + (Dz f t r z) ^ 2) := by
  simp only [Dzz]
  have hfun : (fun q => Dz (fun t r z => Real.exp (f t r z)) t r q)
      = fun q => Real.exp (f t r q) * Dz f t r q := by
    funext q; exact Dz_exp hf t r q
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun q => Real.exp (f t r q)) z := (hf.hz t r z).exp
  have hd2 : DifferentiableAt ℝ (fun q => Dz f t r q) z := hf.hzz t r z
  change deriv ((fun q => Real.exp (f t r q)) * (fun q => Dz f t r q)) z = _
  rw [deriv_mul hd1 hd2]
  rw [show deriv (fun q => Real.exp (f t r q)) z = Real.exp (f t r z) * Dz f t r z
        from Dz_exp hf t r z]
  simp only [Dz]
  ring

/-- `Δ_5(e^f) = e^f (Δ_5 f + |∇_5 f|²)`. -/
lemma Delta5_exp (hf : Smooth f) (t r z : ℝ) :
    Delta5 (fun t r z => Real.exp (f t r z)) t r z
      = Real.exp (f t r z) * (Delta5 f t r z + grad5Sq f t r z) := by
  simp only [Delta5, grad5Sq]
  rw [Drr_exp hf, Dr_exp hf, Dzz_exp hf]
  ring

/-! ## Smoothness closure and the weight identities -/

lemma smooth_mul (hF : Smooth F) (hG : Smooth G') :
    Smooth (fun t r z => F t r z * G' t r z) where
  ht := by intro t r z; exact (hF.ht t r z).mul (hG.ht t r z)
  hr := by intro t r z; exact (hF.hr t r z).mul (hG.hr t r z)
  hz := by intro t r z; exact (hF.hz t r z).mul (hG.hz t r z)
  hrr := by
    intro t r z
    have hfun : (fun p => Dr (fun t r z => F t r z * G' t r z) t p z)
        = fun p => Dr F t p z * G' t p z + F t p z * Dr G' t p z := by
      funext p; exact Dr_mul hF hG t p z
    rw [hfun]
    exact ((hF.hrr t r z).mul (hG.hr t r z)).add ((hF.hr t r z).mul (hG.hrr t r z))
  hzz := by
    intro t r z
    have hfun : (fun q => Dz (fun t r z => F t r z * G' t r z) t r q)
        = fun q => Dz F t r q * G' t r q + F t r q * Dz G' t r q := by
      funext q; exact Dz_mul hF hG t r q
    rw [hfun]
    exact ((hF.hzz t r z).mul (hG.hz t r z)).add ((hF.hz t r z).mul (hG.hzz t r z))

lemma smooth_exp (hf : Smooth f) : Smooth (fun t r z => Real.exp (f t r z)) where
  ht := by intro t r z; exact (hf.ht t r z).exp
  hr := by intro t r z; exact (hf.hr t r z).exp
  hz := by intro t r z; exact (hf.hz t r z).exp
  hrr := by
    intro t r z
    have hfun : (fun p => Dr (fun t r z => Real.exp (f t r z)) t p z)
        = fun p => Real.exp (f t p z) * Dr f t p z := by
      funext p; exact Dr_exp hf t p z
    rw [hfun]
    exact ((hf.hr t r z).exp).mul (hf.hrr t r z)
  hzz := by
    intro t r z
    have hfun : (fun q => Dz (fun t r z => Real.exp (f t r z)) t r q)
        = fun q => Real.exp (f t r q) * Dz f t r q := by
      funext q; exact Dz_exp hf t r q
    rw [hfun]
    exact ((hf.hz t r z).exp).mul (hf.hzz t r z)

lemma smooth_wgt (hf : Smooth f) : Smooth (wgt f) :=
  smooth_mul smooth_rhoSq (smooth_exp hf)

lemma Dt_wgt (hf : Smooth f) (t r z : ℝ) :
    Dt (wgt f) t r z = wgt f t r z * Dt f t r z := by
  have hE : Smooth (fun t r z => Real.exp (f t r z)) := smooth_exp hf
  change Dt (fun t r z => rhoSq t r z * Real.exp (f t r z)) t r z = _
  rw [Dt_mul smooth_rhoSq hE]
  have hDtρ : Dt rhoSq t r z = 0 := by simp [Dt, rhoSq, deriv_const]
  rw [hDtρ, zero_mul, zero_add, Dt_exp hf]
  simp only [wgt, rhoSq]
  ring

lemma Dr_wgt (hf : Smooth f) (t r z : ℝ) :
    Dr (wgt f) t r z = Real.exp (f t r z) * (2 * r + r ^ 2 * Dr f t r z) := by
  have hE : Smooth (fun t r z => Real.exp (f t r z)) := smooth_exp hf
  change Dr (fun t r z => rhoSq t r z * Real.exp (f t r z)) t r z = _
  rw [Dr_mul smooth_rhoSq hE, Dr_rhoSq, Dr_exp hf]
  simp only [rhoSq]
  ring

lemma Dz_wgt (hf : Smooth f) (t r z : ℝ) :
    Dz (wgt f) t r z = Real.exp (f t r z) * (r ^ 2 * Dz f t r z) := by
  have hE : Smooth (fun t r z => Real.exp (f t r z)) := smooth_exp hf
  change Dz (fun t r z => rhoSq t r z * Real.exp (f t r z)) t r z = _
  rw [Dz_mul smooth_rhoSq hE, Dz_exp hf]
  have hDzρ : Dz rhoSq t r z = 0 := by simp [Dz, rhoSq, deriv_const]
  rw [hDzρ, zero_mul, zero_add]
  simp only [rhoSq]
  ring

/-- `Δ_μ(ρ²e^f) = ρ²e^f (Δ_5f + |∇_5f|²)`. -/
lemma DeltaMu_wgt (hf : Smooth f) (t r z : ℝ) (hr : r ≠ 0) :
    DeltaMu (wgt f) t r z = wgt f t r z * (Delta5 f t r z + grad5Sq f t r z) := by
  change DeltaMu (fun t r z => r ^ 2 * Real.exp (f t r z)) t r z = _
  rw [DeltaMu_rhoSq_mul (smooth_exp hf) t r z hr, Delta5_exp hf]
  simp only [wgt]
  ring

lemma bDotGrad_mul (hF : Smooth F) (hG : Smooth G') (t r z : ℝ) :
    bDotGrad b (fun t r z => F t r z * G' t r z) t r z
      = bDotGrad b F t r z * G' t r z + F t r z * bDotGrad b G' t r z := by
  simp only [bDotGrad, Dr_mul hF hG, Dz_mul hF hG]
  ring

/-- `b·∇(ρ²e^f) = e^f (2ρ b^ρ + ρ² b·∇_5f)`. -/
lemma bDotGrad_wgt (hf : Smooth f) (t r z : ℝ) :
    bDotGrad b (wgt f) t r z
      = Real.exp (f t r z) * (2 * r * (b t r z).1 + r ^ 2 * bDotGrad b f t r z) := by
  have hE : Smooth (fun t r z => Real.exp (f t r z)) := smooth_exp hf
  have hmul := bDotGrad_mul (b := b) (F := rhoSq) (G' := fun t r z => Real.exp (f t r z))
    smooth_rhoSq hE t r z
  change bDotGrad b (fun t r z => rhoSq t r z * Real.exp (f t r z)) t r z = _
  rw [hmul]
  have hDρ : Dr rhoSq t r z = 2 * r := Dr_rhoSq t r z
  have hDzρ : Dz rhoSq t r z = 0 := by simp [Dz, rhoSq, deriv_const]
  simp only [bDotGrad]
  rw [hDρ, hDzρ, Dr_exp hf, Dz_exp hf]
  simp only [rhoSq]
  ring

/-! ## The main identity (`prop:timedep`) -/

/-- **`prop:timedep`, derivative identity.**
Let `Γ = w·h` with `h = ρ²e^f`, and let `Γ` solve the swirl transport equation
`∂_tΓ + b·∇Γ = νΔ_μΓ`.  Then at every critical point of `w` (`ρ>0`),
`∂_t w = νΔ_μ w + G w` with `G` as in the paper. -/
theorem prop_timedep
    (ν : ℝ) (b : Meridional) (Γ w f : ℝ → ℝ → ℝ → ℝ)
    (hΓ : Γ = fun t r z => w t r z * wgt f t r z)
    (hw : Smooth w) (hf : Smooth f)
    (htr : TransportEq ν b Γ)
    (t r z : ℝ) (hr : r ≠ 0) (hcrit : CriticalPoint w t r z) :
    Dt w t r z = ν * DeltaMu w t r z + G ν b f t r z * w t r z := by
  have hS : Smooth (wgt f) := smooth_wgt hf
  -- the transport equation, with `Γ` unfolded to `w·h`
  have hstar : Dt Γ t r z + bDotGrad b Γ t r z = ν * DeltaMu Γ t r z := htr t r z
  rw [hΓ] at hstar
  -- expand each of the three terms
  have hDt : Dt (fun t r z => w t r z * wgt f t r z) t r z
      = Dt w t r z * wgt f t r z + w t r z * Dt (wgt f) t r z :=
    Dt_mul hw hS t r z
  have hDth : Dt (wgt f) t r z = wgt f t r z * Dt f t r z := Dt_wgt hf t r z
  have hb : bDotGrad b (fun t r z => w t r z * wgt f t r z) t r z
      = bDotGrad b w t r z * wgt f t r z + w t r z * bDotGrad b (wgt f) t r z :=
    bDotGrad_mul hw hS t r z
  have hbw : bDotGrad b w t r z = 0 := by
    simp only [bDotGrad, hcrit.1, hcrit.2, mul_zero, add_zero]
  have hD : DeltaMu (fun t r z => w t r z * wgt f t r z) t r z
      = DeltaMu w t r z * wgt f t r z + w t r z * DeltaMu (wgt f) t r z
        + 2 * (Dr w t r z * Dr (wgt f) t r z + Dz w t r z * Dz (wgt f) t r z) :=
    DeltaMu_mul hw hS t r z
  have hcross : Dr w t r z * Dr (wgt f) t r z + Dz w t r z * Dz (wgt f) t r z = 0 := by
    rw [hcrit.1, hcrit.2]; ring
  rw [hDt, hb, hD, hcross, hbw, hDth] at hstar
  simp only [zero_mul, mul_zero, add_zero] at hstar
  -- the two bracket identities
  have hΔ : DeltaMu (wgt f) t r z = wgt f t r z * (Delta5 f t r z + grad5Sq f t r z) :=
    DeltaMu_wgt hf t r z hr
  have hB : bDotGrad b (wgt f) t r z
      = Real.exp (f t r z) * (2 * r * (b t r z).1 + r ^ 2 * bDotGrad b f t r z) :=
    bDotGrad_wgt hf t r z
  rw [hΔ, hB] at hstar
  -- abbreviations
  obtain ⟨H, hH⟩ : ∃ H, H = wgt f t r z := ⟨_, rfl⟩
  -- `hstar` and the goal, in terms of `H`
  have hHpos : H ≠ 0 := by
    rw [hH]
    simp only [wgt]
    exact mul_ne_zero (pow_ne_zero 2 hr) (Real.exp_ne_zero _)
  have hHE : H = r ^ 2 * Real.exp (f t r z) := by rw [hH]; rfl
  -- `e^f(2ρb^ρ + ρ²b·∇f) = H (2b^ρ/ρ + b·∇f)`
  have hsplit : Real.exp (f t r z) * (2 * r * (b t r z).1 + r ^ 2 * bDotGrad b f t r z)
      = H * (2 * (b t r z).1 / r + bDotGrad b f t r z) := by
    rw [hHE]; field_simp
  rw [hsplit] at hstar
  -- divide `hstar` by `H`
  have key : Dt w t r z * H
      = (ν * DeltaMu w t r z + G ν b f t r z * w t r z) * H := by
    rw [hH] at hstar ⊢
    simp only [G, R, V0]
    linarith [hstar]
  exact mul_right_cancel₀ hHpos key

/-! ## The order reformulation `G ≤ 0 ↔ ∂_t f ≥ R` -/

/-- `G = R − ∂_t f` (definitional unwinding). -/
theorem G_eq_R_sub (ν : ℝ) (b : Meridional) (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) :
    G ν b f t r z = R ν b f t r z - Dt f t r z := rfl

/-- `G ≤ 0` iff `∂_t f ≥ R` — the paper's "amplitude non-increasing" criterion. -/
theorem G_nonpos_iff (ν : ℝ) (b : Meridional) (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) :
    G ν b f t r z ≤ 0 ↔ Dt f t r z ≥ R ν b f t r z := by
  rw [G_eq_R_sub]
  constructor <;> intro h <;> linarith

/-!
## GAP: what is *not* formalized here

The paper's `prop:timedep` has a second half which is *not* a pointwise derivative
identity and is not attempted above:

1. **The sup step.**  For `f = ψ(x) + c(t)` the pointwise criterion reads
   `c'(t) ≥ R(x)` for every `x`, hence `c'(t) ≥ sup_x R(x)`.
   Formally this needs `Real.sSup_le` plus the nonemptiness/boundedness of the range
   of `R`; it is routine (`∀x, a ≤ R x ↔ a ≤ sSup (range R)`) but is a global-`x`
   statement that the current probe does not set up (no hypothesis that `x ↦ R(x)`
   is bounded above is available at this level).

2. **Backward decay forces `c' ≤ 0`.**  The paper writes: "backward decay of
   `w = Φ e^{-f}` forces `c' ≤ 0`".  This is *not* a derivative computation: it
   combines `sup_x |w| = e^{-c(t)} sup_x |Φ|` with the uniform backward bound
   `|Φ(t)| ≤ C₁/(2(1+√-t))` (`prop:bound`) and the Feynman–Kac/maximum-principle
   rigidity of `thm:star2`.  That is the global analytic layer, out of scope here.

3. **The additive-family algebra `G = R_ψ − c'(t)`.**  To turn `G` into the paper's
   form for `f = ψ(x)+c(t)` one needs `∂_t f = c'` and `∂_ρ f = ∂_ρψ`, `∂_ζ f = ∂_ζψ`
   from `f(t,ρ,ζ) = ψ(ρ,ζ)+c(t)`; that is another (short) chain-rule computation
   analogous to `Dt_wgt` and is likewise not needed for the derivative identity.
-/

end Liouville.Probe
