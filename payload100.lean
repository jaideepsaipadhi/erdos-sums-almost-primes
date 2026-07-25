/-- A1 step 3b: the Euler factors for the absolute values are multipliable. -/
theorem zOmega_factors_multipliable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) :
    Multipliable (fun p : Nat.Primes => (1 - Norm.norm z * ((p:ℝ) ^ (-s)))⁻¹) := by
  have hlt : ∀ p : Nat.Primes, Norm.norm z * ((p:ℝ) ^ (-s)) < 1 := by
    intro p
    have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by
      exact_mod_cast p.2.two_le
    have h2s : (0:ℝ) < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hps : ((p:ℕ):ℝ) ^ (-s) ≤ (2:ℝ) ^ (-s) := by
      rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ ((p:ℕ):ℝ)),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      gcongr
    have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
    have hinv : (2:ℝ) ^ (-s) = ((2:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    have hinvpos : (0:ℝ) < ((2:ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
    calc Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) ≤ Norm.norm z * ((2:ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_left hps hznn
      _ = Norm.norm z * ((2:ℝ) ^ s)⁻¹ := by rw [hinv]
      _ < 1 := by
          have hkey : Norm.norm z * ((2:ℝ) ^ s)⁻¹ < ((2:ℝ) ^ s) * ((2:ℝ) ^ s)⁻¹ :=
            mul_lt_mul_of_pos_right hz hinvpos
          rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
  have hpos : ∀ p : Nat.Primes, (0:ℝ) < (1 - Norm.norm z * ((p:ℝ) ^ (-s)))⁻¹ := by
    intro p
    apply inv_pos.mpr
    have := hlt p
    linarith
  apply Real.multipliable_of_summable_log hpos
  sorry
