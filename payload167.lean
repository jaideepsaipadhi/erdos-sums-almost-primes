/-- Radius version of the p >= 3 half-bound: with ||z|| <= r and
r * 3^(-s) <= 1/2, every prime p >= 3 gives ||z|| p^(-s) <= 1/2.
Stated alongside the 3/2 version so nothing already proven changes. -/
theorem zOmega_half_of_three_le_radius (s : ℝ) (r : ℝ) (hr0 : 0 ≤ r) (z : ℂ)
    (hz : Norm.norm z ≤ r) (hrs : r * ((3:ℝ) ^ (-s)) ≤ 1/2) {p : ℕ} (hp3 : 3 ≤ p) :
    Norm.norm z * ((p:ℝ) ^ (-s)) ≤ 1/2 := by
  have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
  have hps : (p:ℝ) ^ (-s) ≤ (3:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ (p:ℝ)),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ (3:ℝ))]
    gcongr
  have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
  calc Norm.norm z * ((p:ℝ) ^ (-s)) ≤ r * ((3:ℝ) ^ (-s)) := by
        apply mul_le_mul hz hps (by positivity) hr0
    _ ≤ 1/2 := hrs
