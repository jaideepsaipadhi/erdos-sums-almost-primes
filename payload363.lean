/-- The derivative contour integral converges as s -> 1+, by dominated
convergence.  M is the same first-derivative bound lemma_3_8_integral_r1
carries -- no new hypothesis. -/
theorem deriv_contour_integral_tendsto (i : ℕ)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds f1))
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ s : ℝ, s ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta)
        * cBracket (f s) s (circleMap 0 (2:ℝ) theta)) ≤ M)
    (hcont : ∀ s : ℝ, s ∈ Set.Ioi (1:ℝ) → Continuous (fun theta : ℝ =>
      deriv (circleMap 0 (2:ℝ)) theta
        * ((1 / circleMap 0 (2:ℝ) theta) ^ i
          * ((circleMap 0 (2:ℝ) theta)⁻¹
            * (G2manu s (circleMap 0 (2:ℝ) theta)
              * cBracket (f s) s (circleMap 0 (2:ℝ) theta)))))) :
    Filter.Tendsto (fun s : ℝ =>
        ∫ theta in Set.Ioc (0:ℝ) (2 * Real.pi),
          deriv (circleMap 0 (2:ℝ)) theta
            * ((1 / circleMap 0 (2:ℝ) theta) ^ i
              * ((circleMap 0 (2:ℝ) theta)⁻¹
                * (G2manu s (circleMap 0 (2:ℝ) theta)
                  * cBracket (f s) s (circleMap 0 (2:ℝ) theta)))))
      (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (∫ theta in Set.Ioc (0:ℝ) (2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹
              * G2deriv1 f1 (circleMap 0 (2:ℝ) theta))))) := by
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hcont s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with theta
    exact contour_integrand_bound_gen i M hM0 theta
      (G2manu s (circleMap 0 (2:ℝ) theta)
        * cBracket (f s) s (circleMap 0 (2:ℝ) theta)) (hM s hs theta)
  · exact MeasureTheory.integrable_const M
  · filter_upwards with theta
    exact deriv_integrand_tendsto i theta f f1 hfc
