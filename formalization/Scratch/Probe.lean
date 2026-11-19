import Mathlib

open Real

-- 探针：deriv 的第二次求导、ring 能不能关掉一个带 1/ρ 的恒等式
example (A Aρ Aρρ Aζζ ρ : ℝ) (hρ : ρ ≠ 0)
    (h : Aρρ + 3 * ρ⁻¹ * Aρ + Aζζ = ρ⁻¹ * (ρ * Aρρ + 3 * Aρ) + Aζζ) : True := by
  trivial

#check @deriv
#check @HasDerivAt.congr_of_eventuallyEq
#check @DifferentiableAt
#check @Real.deriv_pow
#check @norm_integral_le_of_norm_le_const
#check @intervalIntegral.integral_deriv_eq_sub
