/-- The contour integral converges as s -> 1+, by dominated convergence.
M0 is a hypothesis: sup over s in (1,2), |z| = 2 of ||G2manu s z||, the
analogue of the manuscript's M = 326 (Lemma 3.7) at our radius.  Certified
numerically there, so assumed here, as with M1. -/
theorem contour_integral_tendsto (i : ℕ) (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ s : ℝ, s ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    Filter.Tendsto (fun s : ℝ =>
        ∫ theta in Set.Ioc (0:ℝ) (2 * Real.pi),
          deriv (circleMap 0 (2:ℝ)) theta
            * ((1 / circleMap 0 (2:ℝ) theta) ^ i
              * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2manu s (circleMap 0 (2:ℝ) theta))))
      (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (∫ theta in Set.Ioc (0:ℝ) (2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2at1 (circleMap 0 (2:ℝ) theta))))) := by
  have hR : (0:ℝ) < 2 := by norm_num
  have hne : ∀ t : ℝ, circleMap 0 (2:ℝ) t ≠ 0 :=
    fun t => circleMap_ne_center (ne_of_gt hR)
  have hdcm : ∀ theta : ℝ, Norm.norm (deriv (circleMap 0 (2:ℝ)) theta) = 2 := by
    intro theta
    rw [deriv_circleMap, norm_mul, Complex.norm_I]
    simp [circleMap]
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2:ℝ) theta) = 2 := by
    intro theta
    simp [circleMap]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M0)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hkap : 0 < kappaFac s := kappaFac_pos s hs (cFac_pos s hs)
    exact (contour_integrand_continuous s (le_of_lt hs) hkap i).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with theta
    rw [norm_mul, norm_mul, norm_mul, hdcm, norm_pow, norm_div, norm_one, hnorm,
      norm_inv, hnorm]
    have hb := hM0 s hs theta
    have hp2 : ((2:ℝ))⁻¹ ^ i ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      rw [inv_le_one_iff₀]
      right; norm_num
    calc (2:ℝ) * ((1 / (2:ℝ)) ^ i * ((2:ℝ)⁻¹ * Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta))))
        = ((1 / (2:ℝ)) ^ i) * Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta)) := by
          field_simp
      _ ≤ 1 * Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta)) := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [one_div]; exact hp2
      _ = Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta)) := one_mul _
      _ ≤ M0 := hb
  · exact MeasureTheory.integrable_const M0
  · filter_upwards with theta
    exact contour_integrand_tendsto i theta
