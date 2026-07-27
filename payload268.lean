/-- The log of the real regularised p >= 3 product is the sum of the logs.
This is what turns hasDerivAt_log_series (a statement about the tsum) into a
statement about the product, i.e. about log G2 restricted to its p >= 3 part. -/
theorem log_reg_tprod_real (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Real.log (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * (((p:ℕ):ℝ)) ^ (-s))⁻¹ * (1 - (((p:ℕ):ℝ)) ^ (-s)) ^ z)
      = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-Real.log (1 - z * (((p:ℕ):ℝ)) ^ (-s))
          + z * Real.log (1 - (((p:ℕ):ℝ)) ^ (-s))) := by
  have hlogeq : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      Real.log ((1 - z * (((p:ℕ):ℝ)) ^ (-s))⁻¹ * (1 - (((p:ℕ):ℝ)) ^ (-s)) ^ z)
        = -Real.log (1 - z * (((p:ℕ):ℝ)) ^ (-s))
          + z * Real.log (1 - (((p:ℕ):ℝ)) ^ (-s)) := by
    intro p
    have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
    have hppos : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
    have hthird : (((p:ℕ):ℝ)) ^ (-s) ≤ 1/3 := by
      have h1 : (((p:ℕ):ℝ)) ^ (-s) ≤ (((p:ℕ):ℝ)) ^ (-(1:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      rw [Real.rpow_neg_one] at h1
      have h2 : ((((p:ℕ):ℝ)))⁻¹ ≤ 1/3 := by
        rw [inv_le_comm₀ hp0 (by norm_num)]
        linarith
      linarith
    have hzabs := abs_le.mp hz
    have hden : (0:ℝ) < 1 - z * (((p:ℕ):ℝ)) ^ (-s) := by
      nlinarith [hzabs.2, hppos, hthird]
    have hbase : (0:ℝ) < 1 - (((p:ℕ):ℝ)) ^ (-s) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_rpow hbase]
  rw [log_tprod_real (fun p => reg_factor_real_pos (p:ℕ) p.2.2 s hs z hz)
    (reg_multipliable_three_real s hs z hz)
    (by
      have hsum := (prime_correction_summable s hs z hz).of_abs
      apply hsum.congr
      intro p
      exact (hlogeq p).symm)]
  exact tsum_congr hlogeq
