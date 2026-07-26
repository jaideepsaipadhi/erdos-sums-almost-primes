/-- Radius version of the p=2 factor bound: ||z|| * 2^(-s) < 1 when ||z|| <= r < 2^s. -/
theorem two_factor_lt_one_radius (s : ℝ) (r : ℝ) (hr0 : 0 ≤ r) (hrs : r < (2:ℝ) ^ s)
    (z : ℂ) (hz : Norm.norm z ≤ r) :
    Norm.norm z * ((2:ℝ) ^ (-s)) < 1 := by
  have h2s : (0:ℝ) < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hinv : (2:ℝ) ^ (-s) = ((2:ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
  have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
  rw [hinv]
  have hlt : Norm.norm z < (2:ℝ) ^ s := lt_of_le_of_lt hz hrs
  have hinvpos : (0:ℝ) < ((2:ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
  have hkey := mul_lt_mul_of_pos_right hlt hinvpos
  rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
