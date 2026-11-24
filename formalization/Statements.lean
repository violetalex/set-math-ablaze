/-
挑战文件：`statement` 门用的独立陈述。

这里的每一条都不是证明，而是**我们声称证了什么**。它由不参与形式化的人按论文
逐字重写，`mathlean check` 会把每个 `PROVED` 声明的类型与这里的 `Prop` 做定义等价
比较——只比类型，不读证明。

命名约定：`Challenge.<Lean 声明名>`。缺一条就是失败，因为那意味着有一条
`PROVED` 命名的陈述没有经过独立重述。
-/

import Mathlib
import Liouville

open Real Set Filter MeasureTheory
open scoped Interval

namespace Challenge

/-- 台账 A34（论文 A，`prop:bound` 的积分步）。

设 Γ 轴正则（Γ(0,ζ,t)=0 且 Γ/ρ² 在 ρ→0⁺ 有极限）、ρ↦Γ(ρ,ζ,t) 在 [0,∞) 上可微、
∂_ρΓ 在每个 [0,ρ] 上区间可积，并满足由 (H2) 得到的逐点界 |∂_ρΓ| ≤ C₁ρ/R；
则 |Φ| ≤ C₁/(2(1+√(-t))) 对一切 ρ ≥ 0、ζ、t ≤ 0。 -/
def Liouville.PhiExt_bound : Prop :=
  ∀ (Γ : ℝ → ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ → ℝ) (C₁ : ℝ),
    (0 ≤ C₁) →
    (∀ ζ t, Γ 0 ζ t = 0) →
    (∀ ζ t, ∀ ρ, 0 ≤ ρ → DifferentiableAt ℝ (fun r => Γ r ζ t) ρ) →
    (∀ ζ t, ∀ ρ, 0 ≤ ρ →
      IntervalIntegrable (deriv (fun r => Γ r ζ t)) volume 0 ρ) →
    (∀ ρ ζ t, 0 ≤ ρ →
      |deriv (fun r => Γ r ζ t) ρ| ≤ C₁ * ρ / Liouville.R ρ ζ t) →
    (∀ ζ t, Tendsto (fun ρ => Γ ρ ζ t / ρ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Φ₀ ζ t))) →
    ∀ ρ ζ t, 0 ≤ ρ → t ≤ 0 →
      |Liouville.PhiExt Γ Φ₀ ρ ζ t| ≤ C₁ / (2 * (1 + Real.sqrt (-t)))

/-- 台账 A35：A34 的推论，反向衰减的逐点一致形式。 -/
def Liouville.PhiExt_bound_tendsto : Prop :=
  ∀ (Γ : ℝ → ℝ → ℝ → ℝ) (Φ₀ : ℝ → ℝ → ℝ) (C₁ : ℝ),
    (0 ≤ C₁) →
    (∀ ζ t, Γ 0 ζ t = 0) →
    (∀ ζ t, ∀ ρ, 0 ≤ ρ → DifferentiableAt ℝ (fun r => Γ r ζ t) ρ) →
    (∀ ζ t, ∀ ρ, 0 ≤ ρ →
      IntervalIntegrable (deriv (fun r => Γ r ζ t)) volume 0 ρ) →
    (∀ ρ ζ t, 0 ≤ ρ →
      |deriv (fun r => Γ r ζ t) ρ| ≤ C₁ * ρ / Liouville.R ρ ζ t) →
    (∀ ζ t, Tendsto (fun ρ => Γ ρ ζ t / ρ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Φ₀ ζ t))) →
    ∀ ε, 0 < ε → ∃ T, ∀ t, t ≤ T → ∀ ρ ζ, 0 ≤ ρ →
      |Liouville.PhiExt Γ Φ₀ ρ ζ t| ≤ ε

end Challenge
