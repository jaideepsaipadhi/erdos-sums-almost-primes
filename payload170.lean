/-- A1 at radius 3/2 (the form Lemma 2.2 uses). -/
theorem zOmega_summable (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3/2) :
    Summable (fun n : ℕ => Norm.norm (zOmegaHom s z n)) := by
  apply zOmega_summable_radius s hs (3/2) (by norm_num) _ _ z hz
  · have h3 : (3:ℝ) ^ (-s) ≤ (3:ℝ) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    have h3one : (3:ℝ) ^ (-(1:ℝ)) = 1/3 := by
      rw [Real.rpow_neg_one]
      norm_num
    rw [h3one] at h3
    linarith
  · have h2 : (2:ℝ) ^ (1:ℝ) ≤ (2:ℝ) ^ s := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rw [Real.rpow_one] at h2
    linarith
