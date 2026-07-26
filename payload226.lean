theorem prime_correction_bound_complex_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 5/2) :
    ‖(-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)‖
      ≤ 20 * (p:ℝ) ^ (-2*s) := by
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
  have hza_lt1 : ‖(z:ℂ) * (a:ℂ)‖ < 1 := by linarith
  have hr1 := complex_log_bound ((z:ℂ) * (a:ℂ)) hza_lt1
  have hr2 := log_bound_combined a (by rw [abs_of_pos ha_pos]; linarith)
  have hr1bound : ‖z * (a:ℂ)‖^2 / (1 - ‖z * (a:ℂ)‖) ≤ 12.5 * a^2 := by
    have h1 : ‖z * (a:ℂ)‖ ≤ (5/2) * a := by
      rw [norm_mul, hane]; nlinarith [hz]
    have h2 : (1:ℝ)/2 ≤ 1 - ‖z * (a:ℂ)‖ := by linarith [hza_le]
    have h3 : ‖z * (a:ℂ)‖^2 ≤ 6.25 * a^2 := by
      nlinarith [h1, norm_nonneg (z * (a:ℂ))]
    calc ‖z * (a:ℂ)‖^2 / (1 - ‖z * (a:ℂ)‖) ≤ ‖z * (a:ℂ)‖^2 / (1/2) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h2
      _ = 2 * ‖z * (a:ℂ)‖^2 := by ring
      _ ≤ 2 * (6.25 * a^2) := by linarith [h3]
      _ = 12.5 * a^2 := by ring
  have hkey : (-Complex.log (1 - z * (a:ℂ))) + z * (Real.log (1 - a) : ℂ)
      = -(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)) +
          z * ((Real.log (1 - a) : ℂ) + (a:ℂ)) := by ring
  rw [hkey]
  have hstep1 : ‖-(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖
      ≤ ‖Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ := by
    have := norm_add_le (-(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)))
      (z * ((Real.log (1 - a) : ℂ) + (a:ℂ)))
    rwa [norm_neg] at this
  have hstep2 : ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ ≤ ‖z‖ * (3 * a^2) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have heq : ((Real.log (1 - a) : ℂ) + (a:ℂ)) = ((Real.log (1 - a) + a : ℝ):ℂ) := by
      push_cast; ring
    rw [heq]
    first
    | rw [Complex.norm_real]; exact hr2
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact hr2
  have hfinal_bound : ‖Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)‖ +
      ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ ≤ 12.5 * a^2 + ‖z‖ * (3 * a^2) := by
    linarith [hr1, hr1bound, hstep2]
  calc ‖-(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖
      ≤ ‖Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ := hstep1
    _ ≤ 12.5 * a^2 + ‖z‖ * (3 * a^2) := hfinal_bound
    _ ≤ 12.5 * a^2 + (5/2) * (3 * a^2) := by nlinarith [hz, sq_nonneg a]
    _ = 20 * a^2 := by ring
    _ = 20 * (p:ℝ) ^ (-2*s) := by
        rw [ha_def, ← Real.rpow_natCast ((p:ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
        ring_nf

