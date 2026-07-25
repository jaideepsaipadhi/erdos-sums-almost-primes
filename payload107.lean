/-- A1 step 4b: each Euler factor is at least 1. -/
theorem zOmega_factor_ge_one (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) (p : Nat.Primes) :
    (1:ℝ) ≤ (1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))⁻¹ := by
  have hlt : Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) < 1 := by
    have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.two_le
    have h2s : (0:ℝ) < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hps : ((p:ℕ):ℝ) ^ (-s) ≤ (2:ℝ) ^ (-s) := by
      rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ ((p:ℕ):ℝ)),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      gcongr
    have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
    have hinvpos : (0:ℝ) < ((2:ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
    calc Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) ≤ Norm.norm z * ((2:ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_left hps hznn
      _ = Norm.norm z * ((2:ℝ) ^ s)⁻¹ := by rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      _ < 1 := by
          have hkey := mul_lt_mul_of_pos_right hz hinvpos
          rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
  have hnn : (0:ℝ) ≤ Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) := by positivity
  rw [le_inv_comm₀ (by norm_num) (by linarith)]
  linarith
