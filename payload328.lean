/-- Complex analogue of deriv2_prime_term_bound: the r=2 per-prime derivative
is bounded by 200 log^2 p p^(-2), s-free for s >= 1.
Same crude route: ||z-1|| <= 3, ||(p^s-z)+(p^s-1)|| <= 3p^s,
||p^s-1|| >= (2/3)p^s, ||p^s-z|| >= (1/3)p^s. -/
theorem deriv2_clog_term_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm ((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2 * ((((p:ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))
      ≤ 200 * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ (-(2:ℝ))) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (3:ℝ) ≤ ((p:ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p:ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0:ℝ) < ((p:ℝ)) ^ s := by linarith
  have hpsC : Norm.norm ((((p:ℝ)) ^ s : ℝ) : ℂ) = ((p:ℝ)) ^ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hps0]
  have hlog0 : (0:ℝ) ≤ (Real.log (p:ℝ)) ^ 2 := sq_nonneg _
  have hlogC : Norm.norm (((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2) = (Real.log (p:ℝ)) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (sq_nonneg _)]
  have hz1 : Norm.norm (z - 1) ≤ 3 := by
    calc Norm.norm (z - 1) ≤ Norm.norm z + Norm.norm (1:ℂ) := norm_sub_le z 1
      _ ≤ 2 + 1 := by simp only [norm_one]; linarith
      _ = 3 := by norm_num
  have hsum3 : Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)
      + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) ≤ 3 * ((p:ℝ)) ^ s := by
    calc Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        ≤ Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z))
          + Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) := norm_add_le _ _
      _ ≤ (((p:ℝ)) ^ s + 2) + (((p:ℝ)) ^ s + 1) := by
          have ha : Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)) ≤ ((p:ℝ)) ^ s + 2 := by
            calc Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z))
                ≤ Norm.norm ((((p:ℝ)) ^ s : ℝ) : ℂ) + Norm.norm z := norm_sub_le _ _
              _ ≤ ((p:ℝ)) ^ s + 2 := by rw [hpsC]; linarith
          have hb : Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) ≤ ((p:ℝ)) ^ s + 1 := by
            calc Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
                ≤ Norm.norm ((((p:ℝ)) ^ s : ℝ) : ℂ) + Norm.norm (1:ℂ) := norm_sub_le _ _
              _ ≤ ((p:ℝ)) ^ s + 1 := by rw [hpsC]; simp only [norm_one]
          linarith
      _ ≤ 3 * ((p:ℝ)) ^ s := by linarith
  have hd1 : (2/3) * ((p:ℝ)) ^ s ≤ Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) := by
    have h := norm_sub_norm_le ((((p:ℝ)) ^ s : ℝ) : ℂ) (1:ℂ)
    rw [hpsC] at h
    simp only [norm_one] at h
    linarith
  have hd2 : (1/3) * ((p:ℝ)) ^ s ≤ Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)) := by
    have h := norm_sub_norm_le ((((p:ℝ)) ^ s : ℝ) : ℂ) z
    rw [hpsC] at h
    linarith
  have hd1p : (0:ℝ) < Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) := by linarith
  have hd2p : (0:ℝ) < Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)) := by linarith
  rw [norm_div, norm_mul, norm_pow, norm_pow]
  rw [div_le_iff₀ (by positivity)]
  have hnum : Norm.norm ((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2
        * ((((p:ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)))
      ≤ 9 * (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hlogC, hpsC]
    calc Norm.norm (z - 1) * (Real.log (p:ℝ)) ^ 2 * ((p:ℝ)) ^ s
          * Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        ≤ 3 * (Real.log (p:ℝ)) ^ 2 * ((p:ℝ)) ^ s * (3 * ((p:ℝ)) ^ s) := by
          apply mul_le_mul _ hsum3 (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hps0)
          exact mul_le_mul_of_nonneg_right hz1 hlog0
      _ = 9 * (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by ring
  have hsq1 : (4/9) * ((((p:ℝ)) ^ s)) ^ 2
      ≤ Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2 := by nlinarith [hd1, hps0]
  have hsq2 : (1/9) * ((((p:ℝ)) ^ s)) ^ 2
      ≤ Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2 := by nlinarith [hd2, hps0]
  have hden : (4/81) * ((((p:ℝ)) ^ s)) ^ 4
      ≤ Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2
        * Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2 := by
    nlinarith [hsq1, hsq2, hps0, sq_nonneg (((p:ℝ)) ^ s)]
  have hpow : ((p:ℝ)) ^ (-(2:ℝ)) * ((((p:ℝ)) ^ s)) ^ 2 ≥ 1 := by
    have hsq : ((((p:ℝ)) ^ s)) ^ 2 = ((p:ℝ)) ^ (2*s) := by
      rw [← Real.rpow_natCast (((p:ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
      norm_num
      ring_nf
    rw [hsq, ← Real.rpow_add hp0]
    calc (1:ℝ) = ((p:ℝ)) ^ (0:ℝ) := by rw [Real.rpow_zero]
      _ ≤ ((p:ℝ)) ^ (-(2:ℝ) + 2*s) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hLQ : (0:ℝ) ≤ (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by positivity
  have hkey : 200 * (Real.log (p:ℝ)) ^ 2 * ((p:ℝ)) ^ (-(2:ℝ))
        * ((4/81) * ((((p:ℝ)) ^ s)) ^ 4)
      ≥ 9 * (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by
    have h4 : ((((p:ℝ)) ^ s)) ^ 4 = ((((p:ℝ)) ^ s)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by ring
    rw [h4]
    have hstep : (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2
          * (((p:ℝ)) ^ (-(2:ℝ)) * ((((p:ℝ)) ^ s)) ^ 2)
        ≥ (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hpow hLQ
    calc 200 * (Real.log (p:ℝ)) ^ 2 * ((p:ℝ)) ^ (-(2:ℝ))
          * ((4/81) * (((((p:ℝ)) ^ s)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2))
        = (800/81) * ((Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2
            * (((p:ℝ)) ^ (-(2:ℝ)) * ((((p:ℝ)) ^ s)) ^ 2)) := by ring
      _ ≥ (800/81) * ((Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 * 1) := by
          apply mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (800/81) * ((Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2) := by ring
      _ ≥ 9 * (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by nlinarith [hLQ]
  have hmul : 200 * (Real.log (p:ℝ)) ^ 2 * ((p:ℝ)) ^ (-(2:ℝ))
        * (Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2
          * Norm.norm ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2)
      ≥ 200 * (Real.log (p:ℝ)) ^ 2 * ((p:ℝ)) ^ (-(2:ℝ))
        * ((4/81) * ((((p:ℝ)) ^ s)) ^ 4) := by
    apply mul_le_mul_of_nonneg_left hden
    have : (0:ℝ) < ((p:ℝ)) ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hp0 _
    positivity
  linarith [hnum, hkey, hmul]
