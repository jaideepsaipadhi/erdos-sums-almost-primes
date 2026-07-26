/-- The p = 3 Euler factor is differentiable on the wide disc |z| < 5/2.
Simpler than the general per-prime lemma: no log estimates are needed, only
that 1 - z*3^(-s) is nonvanishing there (|z*3^(-s)| < 5/6 at s = 1) and that
the cpow factor is entire.  The general wide lemma requires p >= 5, so the
p = 3 factor of G2C needs this separate treatment. -/
theorem prime_three_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * ((((3:ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ *
      ((((1 - ((3:ℝ)) ^ (-s) : ℝ)) : ℂ)) ^ z) (Metric.ball 0 (5/2)) := by
  set a : ℝ := ((3:ℝ)) ^ (-s) with ha_def
  have ha_pos : (0:ℝ) < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have h1 : ((3:ℝ)) ^ (-s) ≤ ((3:ℝ)) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rw [Real.rpow_neg_one] at h1
    norm_num at h1
    linarith
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have h1a_ne : ((((1 - a : ℝ))) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza : Norm.norm (z * ((a : ℝ) : ℂ)) < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha_pos]
    calc Norm.norm z * a < (5/2) * a := by
          apply mul_lt_mul_of_pos_right hz ha_pos
      _ ≤ (5/2) * (1/3) := by
          apply mul_le_mul_of_nonneg_left ha_le (by norm_num)
      _ < 1 := by norm_num
  have hne : (1:ℂ) - z * ((a : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have := sub_eq_zero.mp hcon
    rw [← this] at hza
    simp at hza
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · apply DifferentiableAt.inv _ hne
    exact (differentiableAt_const 1).sub (differentiableAt_id.mul (differentiableAt_const _))
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl h1a_ne)
