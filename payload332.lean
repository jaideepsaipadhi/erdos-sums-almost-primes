/-- The z-scaled r=2 bound: ||z|| <= 2 doubles the constant to 400. -/
theorem deriv2_clog_term_bound_z (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm (z * ((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2 * ((((p:ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))))
      ≤ 400 * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ (-(2:ℝ))) := by
  have hbase := deriv2_clog_term_bound p hp s hs z hz
  have hnn : (0:ℝ) ≤ 200 * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ (-(2:ℝ))) := by
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have : (0:ℝ) < (((p:ℝ)) ^ (-(2:ℝ))) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  rw [norm_mul]
  calc Norm.norm z * Norm.norm ((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2
        * ((((p:ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))
      ≤ 2 * (200 * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ (-(2:ℝ)))) := by
        apply mul_le_mul hz hbase (norm_nonneg _) (by norm_num)
    _ = 400 * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ (-(2:ℝ))) := by ring
