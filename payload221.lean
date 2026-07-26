/-- For s > 1 the p = 2 Euler factor is nonzero. -/
theorem two_factor_ne_one (s : ℝ) (hs : 1 < s) :
    (1 : ℂ) - ((2:ℂ)) ^ (-(s:ℂ)) ≠ 0 := by
  have hlt : Norm.norm (((2:ℂ)) ^ (-(s:ℂ))) < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h2 : (2:ℝ) ^ (1:ℝ) < (2:ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h2
    linarith
  intro hcon
  have heq : ((2:ℂ)) ^ (-(s:ℂ)) = 1 := (sub_eq_zero.mp hcon).symm
  rw [heq] at hlt
  simp at hlt
