/-- Complex analogue of deriv_prime_term_bound_uniform: the s-free dominating
bound for the per-prime derivative.  Same constant 27, same crude route, with
norms in place of absolute values. -/
theorem deriv_clog_term_bound_uniform (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
      ≤ 27 * Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := by
  have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
  have hps : (3:ℝ) ≤ (((p:ℕ):ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p:ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0:ℝ) < (((p:ℕ):ℝ)) ^ s := by linarith
  have hlogpos : (0:ℝ) ≤ Real.log ((p:ℕ):ℝ) := Real.log_nonneg (by linarith)
  have hnum : Norm.norm (z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
      ≤ 6 * Real.log ((p:ℕ):ℝ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogpos]
    have h1 : Norm.norm (z - 1) ≤ 3 := by
      calc Norm.norm (z - 1) ≤ Norm.norm z + Norm.norm (1:ℂ) := norm_sub_le z 1
        _ ≤ 2 + 1 := by simp only [norm_one]; linarith
        _ = 3 := by norm_num
    nlinarith [norm_nonneg z, norm_nonneg (z - 1), hz, h1, hlogpos]
  have hd1 : (2/3) * (((p:ℕ):ℝ)) ^ s
      ≤ Norm.norm ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1) := by
    have hre : ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)
        = (((((((p:ℕ):ℝ)) ^ s - 1 : ℝ))) : ℂ) := by push_cast; ring
    rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hd2 : (1/3) * (((p:ℕ):ℝ)) ^ s
      ≤ Norm.norm ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z) := by
    have hge : Norm.norm ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z)
        ≥ Norm.norm ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ))) - Norm.norm z :=
      norm_sub_norm_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hps0] at hge
    linarith
  rw [norm_div, norm_div]
  rw [div_div]
  rw [div_le_iff₀ (by positivity)]
  have hprod : (2/9) * ((((p:ℕ):ℝ)) ^ s) ^ 2
      ≤ Norm.norm ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)
          * Norm.norm ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z) := by
    nlinarith [hd1, hd2, hps0, norm_nonneg ((((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)]
  have hpow2 : (((p:ℕ):ℝ)) ^ (-(2:ℝ)) * ((((p:ℕ):ℝ)) ^ s) ^ 2
      ≥ (((p:ℕ):ℝ)) ^ (-(2:ℝ)) * ((((p:ℕ):ℝ)) ^ (1:ℝ)) ^ 2 := by
    have hmono : ((((p:ℕ):ℝ)) ^ (1:ℝ)) ^ 2 ≤ ((((p:ℕ):ℝ)) ^ s) ^ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (((p:ℕ):ℝ))) hs
      nlinarith [this, Real.rpow_pos_of_pos hp0 (1:ℝ)]
    have : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hp0 _
    nlinarith [hmono, this]
  rw [norm_neg]
  nlinarith [hnum, hprod, hpow2, hlogpos, hps0]
