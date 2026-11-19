import Mathlib
open Real Set Filter MeasureTheory
open scoped Interval

example (C t ρ : ℝ) : (∫ r in (0:ℝ)..ρ, C * r / (1 + Real.sqrt (-t)))
    = C * ρ ^ 2 / (2 * (1 + Real.sqrt (-t))) := by
  have hfun : (fun r => C * r / (1 + Real.sqrt (-t)))
      = (fun r => (C / (1 + Real.sqrt (-t))) * r) := by funext r; ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_id]
  norm_num
  field_simp

-- truth check of the same identity by explicit evaluation at sample data
example : (∫ r in (0:ℝ)..3, (5:ℝ) * r / (1 + 2)) = 5 * 3 ^ 2 / (2 * (1 + 2)) := by
  have hfun : (fun r : ℝ => 5 * r / (1 + 2)) = (fun r => (5 / (1 + 2)) * r) := by funext r; ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_id]; norm_num
