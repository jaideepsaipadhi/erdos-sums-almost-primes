/-- Pointwise: (1-x)^{-1} <= exp(2x) for 0 <= x <= 1/2. -/
theorem inv_one_sub_le_exp (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hone : (0:ℝ) < 1 - x := by linarith
  have hlog : -Real.log (1 - x) ≤ 2 * x := neg_log_one_sub_le x hx0 hx
  have hkey : Real.log ((1 - x)⁻¹) ≤ 2 * x := by
    rw [Real.log_inv]
    exact hlog
  have hpos : (0:ℝ) < (1 - x)⁻¹ := inv_pos.mpr hone
  calc (1 - x)⁻¹ = Real.exp (Real.log ((1 - x)⁻¹)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr hkey
