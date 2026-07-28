/-- The scaled Gamma evaluation at 3: int_{u>0} u^i e^(-3u) du = i!/3^(i+1).
Needed for Theorem 6.1's remainder bound, where the (s-1)^2 weight produces
e^(-3t) under the substitution s = 1 + e^(-t). -/
theorem integral_pow_exp_neg_three_mul (i : ℕ) :
    ∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-(3 * u))
      = (Nat.factorial i : ℝ) / 3 ^ (i + 1) := by
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
    (fun v => v ^ i * Real.exp (-v)) (0:ℝ) (by norm_num : (0:ℝ) < 3)
  simp only [mul_zero] at hcomp
  have hcong : ∀ u ∈ Set.Ioi (0:ℝ),
      u ^ i * Real.exp (-(3 * u)) = ((3 * u) ^ i * Real.exp (-(3 * u))) / 3 ^ i := by
    intro u _
    rw [mul_pow]
    field_simp
    try ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcong]
  rw [MeasureTheory.integral_div, hcomp]
  rw [integral_exp_neg_mul_pow i]
  field_simp
  ring
