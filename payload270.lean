/-- zetaTilde is positive on (1,2]: kappa = zetaTilde * (1 - 2^-s) is positive
and the second factor is. -/
theorem zetaTilde_pos (s : ℝ) (hs : 1 < s) : 0 < zetaTilde s := by
  have hk := kappaFac_pos s hs (cFac_pos s hs)
  rw [kappaFac_eq_zetaTilde s hs] at hk
  have hlt : (2:ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h1 : (2:ℝ) ^ (1:ℝ) < (2:ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h1
    linarith
  have h2 : (0:ℝ) < 1 - (2:ℝ) ^ (-s) := by linarith
  nlinarith [hk, h2]

/-- The p = 2 factor is positive on (1,2]. -/
theorem one_sub_two_pow_pos (s : ℝ) (hs : 1 < s) : (0:ℝ) < 1 - (2:ℝ) ^ (-s) := by
  have hlt : (2:ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h1 : (2:ℝ) ^ (1:ℝ) < (2:ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h1
    linarith
  linarith
