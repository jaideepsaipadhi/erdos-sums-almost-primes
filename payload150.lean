/-- Bound on the correction for the (1 - p^-s)^(-z) family. -/
theorem cpow_neg_sub_one_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm ((((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z) - 1)
      ≤ 8 * (((p:ℕ):ℝ) ^ (-s)) := by
  have hp3R : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast hp
  have hppos : (0:ℝ) < ((p:ℕ):ℝ) := by linarith
  set a : ℝ := ((p:ℕ):ℝ) ^ (-s) with ha
  have hapos : (0:ℝ) < a := by rw [ha]; positivity
  have hale : a ≤ 1/3 := by
    rw [ha]
    have h1 : ((p:ℕ):ℝ) ^ (-s) ≤ ((p:ℕ):ℝ) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : ((p:ℕ):ℝ) ^ (-(1:ℝ)) = 1 / ((p:ℕ):ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / ((p:ℕ):ℝ) ≤ 1/3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3R
    linarith
  have h1a : (0:ℝ) < 1 - a := by linarith
  have hlogbound : Norm.norm (Real.log (1 - a)) ≤ 2 * a := by
    rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
    exact neg_log_one_sub_le a hapos.le (by linarith)
  have hane : (((1 - a : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)) : ℂ) ^ (-z)
      = Complex.exp ((-z) * ((Real.log (1 - a) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hane, ←  Complex.ofReal_log h1a.le]
    ring_nf
  set c : ℂ := (-z) * ((Real.log (1 - a) : ℝ) : ℂ) with hc
  have hcnorm : Norm.norm c ≤ 4 * a := by
    rw [hc, norm_mul, norm_neg, Complex.norm_real]
    calc Norm.norm z * Norm.norm (Real.log (1 - a)) ≤ 2 * (2 * a) := by
          apply mul_le_mul hz hlogbound (norm_nonneg _) (by norm_num)
      _ = 4 * a := by ring
  have hc1 : Norm.norm c ≤ 1 := by
    have : (4:ℝ) * a ≤ 4 * (1/3) := by
      apply mul_le_mul_of_nonneg_left hale (by norm_num)
    linarith
  rw [hcpow]
  calc Norm.norm (Complex.exp c - 1) ≤ 2 * Norm.norm c := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (4 * a) := by linarith
    _ = 8 * a := by ring
