/-- Wide-radius variant (radius 5/2, p >= 5). -/
theorem prime_factor_differentiableOn_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
      (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) (Metric.ball 0 (5/2)) := by
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
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza_lt : ‖z * (a:ℂ)‖ < 1 := by
    have hane : ‖(a:ℂ)‖ = a := by
      first
      | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
      | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
    rw [norm_mul, hane]
    nlinarith [hz, ha_le, ha_pos]
  have h1za_ne : (1:ℂ) - z * (a:ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1:ℝ) = ‖z * (a:ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · have hlin : DifferentiableAt ℂ (fun w : ℂ => (1:ℂ) - w * (a:ℂ)) z := by
      first
      | exact (differentiableAt_const (1:ℂ)).sub (differentiableAt_id.mul_const (a:ℂ))
      | exact (differentiableAt_const (1:ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a:ℂ))
    exact hlin.inv h1za_ne
  · first
    | exact differentiableAt_id.const_cpow (Or.inr h1a_ne)
    | exact differentiableAt_id.const_cpow (Or.inl h1a_ne)
    | exact DifferentiableAt.const_cpow differentiableAt_id (Or.inr h1a_ne)

/-- Wide-radius variant (radius 5/2, p >= 5). -/
theorem correction_differentiableOn_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
      z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) (Metric.ball 0 (5/2)) := by
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
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hane : ‖(a:ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_lt : ‖z * (a:ℂ)‖ < 1 := by
    rw [norm_mul, hane]; nlinarith [hz, ha_le, ha_pos]
  have hre_pos : (0:ℝ) < ((1:ℂ) - z * (a:ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    have hre_le_norm : |z.re| ≤ ‖z‖ := by
      have hns : z.re^2 ≤ Complex.normSq z := by
        have : Complex.normSq z = z.re^2 + z.im^2 := by
          rw [Complex.normSq_apply]; ring
        nlinarith [sq_nonneg z.im, this]
      have hnormsq : ‖z‖^2 = Complex.normSq z := by
        first
        | rw [Complex.norm_eq_abs, Complex.abs_apply, Real.sq_sqrt (Complex.normSq_nonneg z)]
        | rw [Complex.sq_norm]
        | rw [Complex.norm_sq_apply]
        | exact (Complex.normSq_eq_abs z).symm ▸ (Complex.sq_abs z)
        | rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]
      have hsq : z.re^2 ≤ ‖z‖^2 := by rw [hnormsq]; exact hns
      nlinarith [abs_nonneg z.re, norm_nonneg z, sq_abs z.re, hsq]
    have hre_le : z.re * a ≤ ‖z‖ * a := by
      rw [abs_le] at hre_le_norm
      nlinarith [hre_le_norm.2, ha_pos]
    nlinarith [hz, ha_pos, hre_le]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · apply DifferentiableAt.neg
    apply DifferentiableAt.clog
    · first
      | exact (differentiableAt_const (1:ℂ)).sub (differentiableAt_id.mul_const (a:ℂ))
      | exact (differentiableAt_const (1:ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a:ℂ))
    · exact Or.inl hre_pos
  · exact differentiableAt_id.mul_const _

/-- Wide-radius variant (radius 5/2, p >= 5). -/
theorem correction_sum_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)))
      (Metric.ball 0 (5/2)) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 18 * (p:ℝ) ^ (-2*s))
  · have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (18:ℝ) * (p:ℝ) ^ (-2*s) =
        18 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  · intro p
    have hp3 : 5 ≤ (p:ℕ) := p.property.2
    exact correction_differentiableOn_wide (p:ℕ) hp3 s hs
  · exact Metric.isOpen_ball
  · intro p w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hp3 : 5 ≤ (p:ℕ) := p.property.2
    exact prime_correction_bound_complex_wide (p:ℕ) hp3 s hs w hw.le

/-- Wide-radius variant (radius 5/2, p >= 5). -/
theorem G2tailC_eq_exp_sum_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 5/2) :
    G2tailC s z = Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  have hnormsum : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
    have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 18 * (p:ℝ) ^ (-2*s)) := by
      have h2s : -(2*s) < -1 := by linarith
      have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
        Real.summable_nat_rpow.mpr h2s
      have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
        hbase.subtype _
      have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (18:ℝ) * (p:ℝ) ^ (-2*s) =
          18 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
        intro p; ring_nf
      simp_rw [heq]
      exact hsub.mul_left 18
    apply Summable.of_nonneg_of_le
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => by
        have hp3 : 5 ≤ (p:ℕ) := p.property.2
        exact prime_correction_bound_complex_wide (p:ℕ) hp3 s hs z hz)
      hcomp
  have hsummable : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) :=
    Summable.of_norm hnormsum
  have hhassum := hsummable.hasSum
  have hhasprod_exp := hasProd_exp_of_hasSum hhassum
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, Complex.exp
      ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z := by
    intro p
    have hp3 : 5 ≤ (p:ℕ) := p.property.2
    exact (prime_factor_eq_exp_complex_wide (p:ℕ) hp3 s hs z hz).symm
  simp only [heq] at hhasprod_exp
  have hhasprod_G2 := G2tailC_hasProd_wide s hs z hz
  exact (hhasprod_G2.unique hhasprod_exp)

/-- Wide-radius variant (radius 5/2, p >= 5). -/
theorem G2tailC_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2tailC s z) (Metric.ball 0 (5/2)) := by
  have heq : ∀ z ∈ Metric.ball (0:ℂ) (5/2), G2tailC s z = Complex.exp
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ))) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact G2tailC_eq_exp_sum_wide s hs z hz.le
  apply DifferentiableOn.congr _ heq
  exact Complex.differentiable_exp.comp_differentiableOn (correction_sum_differentiableOn_wide s hs)

/-- Wide-radius variant (radius 5/2, p >= 5). -/
theorem G2C_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2C s z) (Metric.ball 0 (5/2)) := by
  unfold G2C
  apply DifferentiableOn.mul
  · exact prime_three_differentiableOn_wide s hs
  · exact G2tailC_differentiableOn_wide s hs
