/-- The r=2 series is continuous in theta on the contour.
Mirrors clog_series_continuous_theta; the global bound holds because circleMap
always lands on |z| = 2, where deriv2_clog_term_bound_z applies. -/
theorem clog2_series_continuous_theta (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (circleMap 0 (2:ℝ) theta * ((circleMap 0 (2:ℝ) theta - 1)
            * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)
            * ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta
              + ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
          / (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
            * (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta) ^ 2))))) := by
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2:ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      clog2_term_continuous_theta (p:ℕ) (by omega) s hs)
    deriv2_bound_uniform_summable_five_z
  intro p theta
  exact deriv2_clog_term_bound_z (p:ℕ) (by omega) s hs
    (circleMap 0 (2:ℝ) theta) (hnorm theta)
