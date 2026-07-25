/-- With ||z|| <= 3/2 and s > 1, every prime p >= 3 satisfies ||z|| p^(-s) <= 1/2. -/
theorem zOmega_half_of_three_le (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z ≤ 3/2) {p : ℕ} (hp3 : 3 ≤ p) :
    Norm.norm z * ((p:ℝ) ^ (-s)) ≤ 1/2 := by
  have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
  have hppos : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (p:ℝ) ^ (-s) ≤ (3:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ (p:ℝ)),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ (3:ℝ))]
    gcongr
  have h3s : (3:ℝ) ^ (-s) ≤ (3:ℝ) ^ (-(1:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have h3one : (3:ℝ) ^ (-(1:ℝ)) = 1/3 := by
    rw [Real.rpow_neg_one]
    norm_num
  have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
  calc Norm.norm z * ((p:ℝ) ^ (-s)) ≤ (3/2) * ((3:ℝ) ^ (-s)) := by
        apply mul_le_mul hz hps (by positivity) (by norm_num)
    _ ≤ (3/2) * (1/3) := by
        rw [←  h3one]
        apply mul_le_mul_of_nonneg_left h3s (by norm_num)
    _ = 1/2 := by norm_num
