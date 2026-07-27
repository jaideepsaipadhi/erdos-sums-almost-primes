/-- G2C is continuous in s on {s // 1 <= s}: the p = 3 factor times the tail.
The p = 3 factor is continuous because 1 - z*3^(-s) stays in the slit plane
and 1 - 3^(-s) stays positive for s >= 1. -/
theorem G2C_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} => G2C (s:ℝ) z) := by
  have hrpow : Continuous (fun s : {s : ℝ // 1 ≤ s} => ((3:ℝ)) ^ (-(s:ℝ))) :=
    (continuous_const_rpow (by norm_num)).comp continuous_subtype_val.neg
  have hlt : ∀ s : {s : ℝ // 1 ≤ s}, ((3:ℝ)) ^ (-(s:ℝ)) ≤ 1/3 := by
    intro s
    have h1 : ((3:ℝ)) ^ (-(s:ℝ)) ≤ ((3:ℝ)) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith [s.2]
    rw [Real.rpow_neg_one] at h1
    norm_num at h1
    linarith
  have hpos : ∀ s : {s : ℝ // 1 ≤ s}, (0:ℝ) < 1 - ((3:ℝ)) ^ (-(s:ℝ)) := by
    intro s
    linarith [hlt s]
  have hlogr : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      Real.log (1 - ((3:ℝ)) ^ (-(s:ℝ)))) :=
    Real.continuousOn_log.comp_continuous (continuous_const.sub hrpow)
      (fun s => ne_of_gt (hpos s))
  have hcpow : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (((1 - ((3:ℝ)) ^ (-(s:ℝ)) : ℝ)) : ℂ) ^ z) := by
    have heq : (fun s : {s : ℝ // 1 ≤ s} =>
        (((1 - ((3:ℝ)) ^ (-(s:ℝ)) : ℝ)) : ℂ) ^ z)
        = fun s : {s : ℝ // 1 ≤ s} =>
          Complex.exp (z * ((Real.log (1 - ((3:ℝ)) ^ (-(s:ℝ))) : ℝ) : ℂ)) := by
      funext s
      rw [ofReal_cpow_eq_exp (1 - ((3:ℝ)) ^ (-(s:ℝ))) (hpos s) z]
      ring_nf
    rw [heq]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hlogr))
  have hzne : ∀ s : {s : ℝ // 1 ≤ s},
      (1 : ℂ) - z * (((((3:ℝ)) ^ (-(s:ℝ)) : ℝ)) : ℂ) ≠ 0 := by
    intro s
    have := one_sub_mem_slitPlane 3 (le_refl 3) (s:ℝ) s.2 z hz
    norm_num at this
    exact Complex.slitPlane_ne_zero this
  have hinv : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (1 - z * (((((3:ℝ)) ^ (-(s:ℝ)) : ℝ)) : ℂ))⁻¹) := by
    apply Continuous.inv₀ _ hzne
    exact continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp hrpow))
  unfold G2C
  exact (hinv.mul hcpow).mul (G2tailC_continuous_s z hz)
