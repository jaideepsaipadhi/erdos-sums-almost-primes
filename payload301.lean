/-- The contour integrand converges pointwise in theta as s -> 1+.
The s-free factors are constant in s; only G2manu moves, and
G2manu_tendsto_G2at1 gives its limit at each point of the contour. -/
theorem contour_integrand_tendsto (i : ℕ) (theta : ℝ) :
    Filter.Tendsto (fun s : ℝ =>
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2manu s (circleMap 0 (2:ℝ) theta))))
      (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (deriv (circleMap 0 (2:ℝ)) theta
        * ((1 / circleMap 0 (2:ℝ) theta) ^ i
          * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2at1 (circleMap 0 (2:ℝ) theta))))) := by
  have hnorm : Norm.norm (circleMap 0 (2:ℝ) theta) ≤ 2 := by
    simp [circleMap]
  have hG2 := G2manu_tendsto_G2at1 (circleMap 0 (2:ℝ) theta) hnorm
  exact (hG2.const_mul _).const_mul _ |>.const_mul _
