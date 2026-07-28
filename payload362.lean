/-- The derivative integrand converges pointwise in theta as s -> 1+. -/
theorem deriv_integrand_tendsto (i : ℕ) (theta : ℝ)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds f1)) :
    Filter.Tendsto (fun s : ℝ =>
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹
              * (G2manu s (circleMap 0 (2:ℝ) theta)
                * cBracket (f s) s (circleMap 0 (2:ℝ) theta)))))
      (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (deriv (circleMap 0 (2:ℝ)) theta
        * ((1 / circleMap 0 (2:ℝ) theta) ^ i
          * ((circleMap 0 (2:ℝ) theta)⁻¹
            * G2deriv1 f1 (circleMap 0 (2:ℝ) theta))))) := by
  have hnorm : Norm.norm (circleMap 0 (2:ℝ) theta) ≤ 2 := by
    simp [circleMap]
  have hbr := cBracket_tendsto_two_arg (circleMap 0 (2:ℝ) theta) hnorm f f1 hfc
  have hG2 := G2deriv_tendsto_at_one (circleMap 0 (2:ℝ) theta) hnorm f f1 hfc hbr
  exact (hG2.const_mul _).const_mul _ |>.const_mul _
