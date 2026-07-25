/-- For 0 <= x <= 1/2, we have -log(1-x) <= 2x.
Route: 1 - x >= exp(-2x), since exp(-2x) <= 1/(1+2x) <= 1-x when x <= 1/2. -/
theorem neg_log_one_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hone : (0:ℝ) < 1 - x := by linarith
  have hstep1 : Real.exp (-(2*x)) ≤ 1 / (1 + 2*x) := by
    have hpos : (0:ℝ) < 1 + 2*x := by linarith
    have hexp : 1 + 2*x ≤ Real.exp (2*x) := by
      have := Real.add_one_le_exp (2*x)
      linarith
    have hexpneg : Real.exp (-(2*x)) = (Real.exp (2*x))⁻¹ := by
      rw [Real.exp_neg]
    rw [hexpneg, one_div]
    apply inv_le_inv_of_le hpos hexp
  have hstep2 : (1:ℝ) / (1 + 2*x) ≤ 1 - x := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + 2*x)]
    nlinarith [hx0, hx]
  have hle : Real.exp (-(2*x)) ≤ 1 - x := le_trans hstep1 hstep2
  have hlog : -(2*x) ≤ Real.log (1 - x) := by
    have := Real.log_le_log (Real.exp_pos (-(2*x))) hle
    rwa [Real.log_exp] at this
  linarith
