/-- The dominating bound for differentiation under the contour.
On |z| = R = 12/5 the non-G2 factors cancel exactly:
  |deriv circleMap| * |(1/z)^i| * |z^(-1)| = R * R^(-i) * (1/R) = R^(-i) <= 1,
so the integrand's s-derivative is bounded by the sup of |d_s G2| alone.

The bound M is a hypothesis: it is
  sup_{t in [1,2], |w| = 12/5} ||d_s G2manu t w||,
the analogue of the manuscript's M1 = 2544 but at radius 12/5 rather than 2.9
(2.9 exceeds the proven analyticity radius 5/2, so the Lean development must
use its own radius). -/
theorem contour_integrand_deriv_bound (i : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (t : ℝ) (theta : ℝ)
    (hbound : Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t) ≤ M) :
    Norm.norm (deriv (circleMap 0 (12/5 : ℝ)) theta
        * ((1 / circleMap 0 (12/5 : ℝ) theta) ^ i
          * ((circleMap 0 (12/5 : ℝ) theta)⁻¹
            * deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t)))
      ≤ M := by
  have hR : (0:ℝ) < 12/5 := by norm_num
  have hnorm : Norm.norm (circleMap 0 (12/5 : ℝ) theta) = 12/5 := by
    simp [circleMap]
  have hne : circleMap 0 (12/5 : ℝ) theta ≠ 0 := circleMap_ne_center (ne_of_gt hR)
  have hdcm : Norm.norm (deriv (circleMap 0 (12/5 : ℝ)) theta) = 12/5 := by
    rw [deriv_circleMap]
    rw [norm_mul, hnorm, Complex.norm_I]
    ring
  rw [norm_mul, norm_mul, norm_mul, hdcm, norm_pow, norm_div, norm_one, hnorm, norm_inv, hnorm]
  have hpow : ((12:ℝ)/5)⁻¹ ^ i ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    rw [inv_le_one_iff₀]
    right
    norm_num
  have hMnn : (0:ℝ) ≤ Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t) :=
    norm_nonneg _
  calc (12/5 : ℝ) * ((1 / (12/5 : ℝ)) ^ i
        * (((12/5 : ℝ))⁻¹
          * Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t)))
      = ((1 / (12/5 : ℝ)) ^ i)
          * Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t) := by
        field_simp
        ring
    _ ≤ 1 * Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t) := by
        apply mul_le_mul_of_nonneg_right _ hMnn
        rw [one_div]
        exact hpow
    _ = Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) t) := one_mul _
    _ ≤ M := hbound
