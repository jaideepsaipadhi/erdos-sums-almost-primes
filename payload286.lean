/-- The contour integrand is continuous in theta.  Discharges the two
measurability obligations and the integrability of F x0 in
hasDerivAt_integral_of_dominated_loc_of_deriv_le: on the circle |z| = 12/5 the
factor (1/z)^i * z^(-1) is continuous (z never vanishes) and G2manu s . is
continuous there by G2manu_differentiableOn_wide. -/
theorem contour_integrand_continuous (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (i : ℕ) :
    Continuous (fun t : ℝ =>
      deriv (circleMap 0 (12/5 : ℝ)) t
        • ((1 / circleMap 0 (12/5 : ℝ) t) ^ i
          • (circleMap 0 (12/5 : ℝ) t)⁻¹ • G2manu s (circleMap 0 (12/5 : ℝ) t))) := by
  have hR : (0:ℝ) < 12/5 := by norm_num
  have hne : ∀ t : ℝ, circleMap 0 (12/5 : ℝ) t ≠ 0 :=
    fun t => circleMap_ne_center (ne_of_gt hR)
  have hcm : Continuous (circleMap 0 (12/5 : ℝ)) := continuous_circleMap 0 _
  have hdcm : Continuous (deriv (circleMap 0 (12/5 : ℝ))) := by
    have : deriv (circleMap 0 (12/5 : ℝ))
        = fun t => circleMap 0 (12/5 : ℝ) t * Complex.I := by
      funext t
      exact deriv_circleMap 0 (12/5 : ℝ) t
    rw [this]
    exact hcm.mul continuous_const
  have hmem : ∀ t : ℝ, circleMap 0 (12/5 : ℝ) t ∈ Metric.closedBall (0:ℂ) (12/5 : ℝ) := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right, abs_circleMap_zero]
    norm_num
  have hG2 : Continuous (fun t : ℝ => G2manu s (circleMap 0 (12/5 : ℝ) t)) := by
    have hcont := (G2manu_differentiableOn_wide s hs hk).continuousOn
    exact hcont.comp_continuous hcm hmem
  apply hdcm.smul
  apply Continuous.smul
  · exact (continuous_const.div hcm (fun t => hne t)).pow i
  · exact (hcm.inv0 (fun t => hne t)).smul hG2
