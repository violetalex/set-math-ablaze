import Liouville.Bound

/-!
# 审计实验：`prop:bound` 积分步的强度 / 锐度

本文件只做实验，不进入 `Liouville` 库。目标：

1. 复现 A34 的陈述本身（打印公理依赖，确认无 `sorryAx`）。
2. 检查 `docs/SPEC.md` §4.1 提出的“锐度见证”
   `Γ = ρ² / (2(1+√-t))` 是否真的满足假设 `hbound`。
   预期：**不满足**，因为 `hbound` 的分母是 `R = 1+√(ρ²+ζ²)+√-t`，
   比 `1+√-t` 大，故 `ρ/R < ρ/(1+√-t)`。
3. 给出真正满足 `hbound` 且非零的 `Γ`（`∂_ρΓ = C₁ρ/R`），证明定理非空洞。
-/

open Real Set Filter MeasureTheory
open scoped Interval

#print axioms Liouville.Phi_bound
#print axioms Liouville.Phi_bound_tendsto

namespace Liouville

noncomputable section

/-! ## 2. SPEC §4.1 的见证不满足 hbound -/

/-- SPEC 提议的见证（C₁ = 1，t = 0，ζ = 0），其 `ρ` 导数应为 `ρ`，在 `ρ=1` 处为 1。 -/
example : deriv (fun r : ℝ => r ^ 2 / (2 * (1 + Real.sqrt (-(0:ℝ))))) (1:ℝ) = 1 := by
  have h : (fun r : ℝ => r ^ 2 / (2 * (1 + Real.sqrt (-(0:ℝ)))))
      = fun r : ℝ => r ^ 2 / 2 := by
    funext r; norm_num
  rw [h]
  simpa using (hasDerivAt_pow 2 (1:ℝ)).div_const 2

/-- `R 1 0 0 = 2`。 -/
example : R 1 0 0 = 2 := by
  unfold R; norm_num

/-- SPEC §4.1 的见证在 `ρ = 1, ζ = 0, t = 0, C₁ = 1` 处**违反** `hbound`：
    需要的上界是 `1 * 1 / R 1 0 0 = 1/2`，而 `∂_ρΓ = 1`。 -/
theorem spec_witness_violates_hbound :
    ¬ (|deriv (fun r : ℝ => r ^ 2 / (2 * (1 + Real.sqrt (-(0:ℝ))))) (1:ℝ)|
        ≤ (1:ℝ) * 1 / R 1 0 0) := by
  have h : (fun r : ℝ => r ^ 2 / (2 * (1 + Real.sqrt (-(0:ℝ)))))
      = fun r : ℝ => r ^ 2 / 2 := by
    funext r; norm_num
  have h1 : deriv (fun r : ℝ => r ^ 2 / (2 * (1 + Real.sqrt (-(0:ℝ))))) (1:ℝ) = 1 := by
    rw [h]; simpa using (hasDerivAt_pow 2 (1:ℝ)).div_const 2
  have hR : R 1 0 0 = 2 := by unfold R; norm_num
  rw [h1, hR]; norm_num

/-! ## 3. 非空洞：极值族 `Γ(ρ) = ∫₀^ρ r/R(r,ζ,t) dr`

对固定的 `ζ,t` 定义 `Γ`。它的 `ρ` 导数逐点等于 `ρ/R`，故 `hbound` 对 `C₁ = 1`
取等号，且 `Γ(0)=0`。`Γ` 非零（`ρ>0` 时被积函数为正），于是 `|Φ|>0`。
-/

/-- 极值族的被积函数。 -/
def gext (ρ ζ t : ℝ) : ℝ := ρ / R ρ ζ t

/-- 极值族 `Γ(ρ,ζ,t) = ∫₀^ρ r / R(r,ζ,t) dr`。 -/
def GammaExt (ρ ζ t : ℝ) : ℝ := ∫ r in (0)..ρ, gext r ζ t

theorem R_continuous (ζ t : ℝ) : Continuous (fun r : ℝ => R r ζ t) := by
  unfold R; fun_prop

theorem gext_continuous (ζ t : ℝ) : Continuous (fun r : ℝ => gext r ζ t) := by
  unfold gext
  exact Continuous.div continuous_id (R_continuous ζ t) (fun r => ne_of_gt (R_pos r ζ t))

/-- 极值族在 `ρ = 0` 处为 0（轴正则）。 -/
theorem GammaExt_zero (ζ t : ℝ) : GammaExt 0 ζ t = 0 := by
  simp [GammaExt]

/-- 极值族的导数正是 `ρ/R`（从而 `hbound` 对 `C₁ = 1` 取等号）。 -/
theorem GammaExt_deriv (ρ ζ t : ℝ) (hρ : 0 ≤ ρ) :
    deriv (fun r => GammaExt r ζ t) ρ = gext ρ ζ t := by
  unfold GammaExt
  exact Continuous.deriv_integral (fun r => gext r ζ t) (gext_continuous ζ t) 0 ρ

/- 极值族非零（手工核验）：在 `ρ>0` 上被积函数 `r/R > 0` 连续，故积分 `> 0`。
    例如 `ρ=1, ζ=0, t=0` 时 `Γ = ∫₀¹ r/(2+r) dr = 1 - 2 log(3/2) ∈ (0,1)`。
    因此 `|Φ| = Γ/ρ² > 0`，`Phi_bound` 的结论不是 `0 ≤ 0` 的空洞形式。 -/

end
end Liouville
