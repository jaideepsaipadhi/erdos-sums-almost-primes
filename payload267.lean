/-- Each regularised factor is positive for real z with |z| <= 2, p >= 3, s >= 1. -/
theorem reg_factor_real_pos (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    0 < (1 - z * ((p:ℝ)) ^ (-s))⁻¹ * (1 - ((p:ℝ)) ^ (-s)) ^ z := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hppos : (0:ℝ) < ((p:ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hthird : ((p:ℝ)) ^ (-s) ≤ 1/3 := by
    have h1 : ((p:ℝ)) ^ (-s) ≤ ((p:ℝ)) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : ((p:ℝ))⁻¹ ≤ 1/3 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hzabs := abs_le.mp hz
  have hden : (0:ℝ) < 1 - z * ((p:ℝ)) ^ (-s) := by
    nlinarith [hzabs.2, hppos, hthird]
  have hbase : (0:ℝ) < 1 - ((p:ℝ)) ^ (-s) := by linarith
  have h1 : (0:ℝ) < (1 - z * ((p:ℝ)) ^ (-s))⁻¹ := inv_pos.mpr hden
  have h2 : (0:ℝ) < (1 - ((p:ℝ)) ^ (-s)) ^ z := Real.rpow_pos_of_pos hbase z
  exact mul_pos h1 h2

/-- The real regularised family is multipliable: its logs are summable
(prime_correction_summable) and each factor is positive. -/
theorem reg_multipliable_three_real (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * (((p:ℕ):ℝ)) ^ (-s))⁻¹ * (1 - (((p:ℕ):ℝ)) ^ (-s)) ^ z) := by
  apply Real.multipliable_of_summable_log
  · intro p
    exact reg_factor_real_pos (p:ℕ) p.2.2 s hs z hz
  · have hsum := (prime_correction_summable s hs z hz).of_abs
    apply hsum.congr
    intro p
    have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
    have hpos := reg_factor_real_pos (p:ℕ) p.2.2 s hs z hz
    have hppos : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
    have hzabs := abs_le.mp hz
    have hthird : (((p:ℕ):ℝ)) ^ (-s) ≤ 1/3 := by
      have h1 : (((p:ℕ):ℝ)) ^ (-s) ≤ (((p:ℕ):ℝ)) ^ (-(1:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      rw [Real.rpow_neg_one] at h1
      have h2 : ((((p:ℕ):ℝ)))⁻¹ ≤ 1/3 := by
        rw [inv_le_comm₀ hp0 (by norm_num)]
        linarith
      linarith
    have hden : (0:ℝ) < 1 - z * (((p:ℕ):ℝ)) ^ (-s) := by
      nlinarith [hzabs.2, hppos, hthird]
    have hbase : (0:ℝ) < 1 - (((p:ℕ):ℝ)) ^ (-s) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_rpow hbase]
    ring
