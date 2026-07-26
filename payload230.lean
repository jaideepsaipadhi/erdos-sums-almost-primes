/-- Wide-radius variant. -/
theorem prime_factor_eq_exp_complex_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 5/2) :
    (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
      Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/5 := by
    rw [ha_def]
    have hp3 : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a:ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z:ℂ) * (a:ℂ)‖ ≤ 1/2 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ (5/2) * (1/5) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt : ‖(z:ℂ) * (a:ℂ)‖ < 1 := by linarith
  have h1za_ne : (1:ℂ) - z * (a:ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1:ℝ) = ‖z * (a:ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)):ℂ) ^ z =
      Complex.exp (Complex.log (((1 - a : ℝ)):ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne]
  have key : Complex.exp ((-Complex.log (1 - z * (a:ℂ))) +
      z * ((Real.log (1 - a) : ℝ):ℂ)) =
      (1 - z * (a:ℂ))⁻¹ * (((1 - a : ℝ)):ℂ) ^ z := by
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_log h1za_ne, hcpow, ← hlog1a,
      show z * Complex.log (((1 - a : ℝ)):ℂ) = Complex.log (((1 - a : ℝ)):ℂ) * z
        from mul_comm _ _]
  exact key.symm
