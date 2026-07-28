/-- Generalised contour bound: the s-free factors contribute at most 1, so the
integrand is bounded by whatever bounds the varying factor.  The r=1 version
contour_integrand_deriv_bound is this at w = the first derivative; r=2 uses it
at w = the second. -/
theorem contour_integrand_bound_gen (i : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (theta : ℝ) (w : ℂ) (hbound : Norm.norm w ≤ M) :
    Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * w)))
      ≤ M := by
  have hR : (0:ℝ) < 2 := by norm_num
  have hnorm : Norm.norm (circleMap 0 (2 : ℝ) theta) = 2 := by
    simp [circleMap]
  have hne : circleMap 0 (2 : ℝ) theta ≠ 0 := circleMap_ne_center (ne_of_gt hR)
  have hdcm : Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta) = 2 := by
    rw [deriv_circleMap, norm_mul, hnorm, Complex.norm_I]
    ring
  rw [norm_mul, norm_mul, norm_mul, hdcm, norm_pow, norm_div, norm_one, hnorm,
    norm_inv, hnorm]
  have hpow : ((2:ℝ))⁻¹ ^ i ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    rw [inv_le_one_iff₀]
    right; norm_num
  have hwnn : (0:ℝ) ≤ Norm.norm w := norm_nonneg _
  calc (2:ℝ) * ((1 / (2:ℝ)) ^ i * (((2:ℝ))⁻¹ * Norm.norm w))
      = ((1 / (2:ℝ)) ^ i) * Norm.norm w := by field_simp
    _ ≤ 1 * Norm.norm w := by
        apply mul_le_mul_of_nonneg_right _ hwnn
        rw [one_div]; exact hpow
    _ = Norm.norm w := one_mul _
    _ ≤ M := hbound
