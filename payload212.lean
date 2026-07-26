/-- G2tailC(1,1) = 1: every factor collapses. -/
theorem G2tailC_one_one : G2tailC 1 1 = 1 := by
  unfold G2tailC
  apply tprod_eq_one
  intro p
  have hp5 : (5:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
  have hlt : ((p:ℕ):ℝ) ^ (-(1:ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    rw [inv_lt_one_iff₀]
    right
    linarith
  exact reg_factor_at_one (((p:ℕ):ℝ) ^ (-(1:ℝ))) (by linarith)

/-- G2C(1,1) = 1 (manuscript section 1). -/
theorem G2C_one_one : G2C 1 1 = 1 := by
  unfold G2C
  rw [G2tailC_one_one, mul_one]
  have h3 : ((3:ℝ)) ^ (-(1:ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    norm_num
  have := reg_factor_at_one (((3:ℝ)) ^ (-(1:ℝ))) (by linarith)
  rw [← this]
  norm_num
