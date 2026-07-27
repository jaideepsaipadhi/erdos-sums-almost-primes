/-- The pointwise bound feeding hasDerivAt_tsum_of_isPreconnected:
|z(z-1) log p / ((p^s-1)(p^s-z))| <= 27 log p p^(-2s) for p >= 3, s >= 1, |z| <= 2.
Crude route: |z(z-1)| <= 6, p^s - 1 >= (2/3)p^s, |p^s - z| >= (1/3)p^s. -/
theorem deriv_prime_term_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(-(z * (z - 1) * Real.log (p:ℝ))
        / ((((p:ℝ)) ^ s - 1) * (((p:ℝ)) ^ s - z)))|
      ≤ 27 * Real.log (p:ℝ) * ((p:ℝ)) ^ (-2*s) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (3:ℝ) ≤ ((p:ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p:ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0:ℝ) < ((p:ℝ)) ^ s := by linarith
  have hzabs := abs_le.mp hz
  have hlogpos : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hnum : |z * (z - 1) * Real.log (p:ℝ)| ≤ 6 * Real.log (p:ℝ) := by
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg hlogpos]
    have h1 : |z| ≤ 2 := hz
    have h2 : |z - 1| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [hzabs.1, hzabs.2]
    nlinarith [abs_nonneg z, abs_nonneg (z - 1), hlogpos]
  have hd1 : (2/3) * ((p:ℝ)) ^ s ≤ ((p:ℝ)) ^ s - 1 := by linarith
  have hd2 : (1/3) * ((p:ℝ)) ^ s ≤ ((p:ℝ)) ^ s - z := by
    linarith [hzabs.2]
  have hden : (2/9) * (((p:ℝ)) ^ s) ^ 2
      ≤ (((p:ℝ)) ^ s - 1) * (((p:ℝ)) ^ s - z) := by
    nlinarith [hd1, hd2, hps0]
  have hdenpos : (0:ℝ) < (((p:ℝ)) ^ s - 1) * (((p:ℝ)) ^ s - z) := by nlinarith [hps0]
  have hsq : (((p:ℝ)) ^ s) ^ 2 = ((p:ℝ)) ^ (2*s) := by
    rw [← Real.rpow_natCast (((p:ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
    norm_num
    ring_nf
  rw [abs_div, abs_neg]
  rw [div_le_iff₀ (by rwa [abs_of_pos hdenpos])]
  rw [abs_of_pos hdenpos]
  have hpow : ((p:ℝ)) ^ (-2*s) * ((p:ℝ)) ^ (2*s) = 1 := by
    rw [← Real.rpow_add hp0]
    norm_num
  nlinarith [hnum, hden, hsq, hpow, hlogpos, hps0]
