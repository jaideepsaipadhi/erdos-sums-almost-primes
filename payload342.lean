/-- C is continuous in theta on the contour: kappa-part, p=3 term, and the
r=1 tail series.  The r=1 analogue of c_bracket_deriv_continuous_theta. -/
theorem c_bracket_continuous_theta (s : ℝ) (hs : 1 ≤ s) (fs : ℝ) :
    Continuous (fun theta : ℝ =>
      circleMap 0 (2:ℝ) theta * (((fs + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)
        + ((-(circleMap 0 (2:ℝ) theta * (circleMap 0 (2:ℝ) theta - 1)
              * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
            / ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
              / ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(circleMap 0 (2:ℝ) theta * (circleMap 0 (2:ℝ) theta - 1)
                  * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                / ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
                  / ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta)))) := by
  have hcm : Continuous (circleMap 0 (2:ℝ)) := continuous_circleMap 0 _
  apply Continuous.add (hcm.mul continuous_const)
  apply Continuous.add
  · exact clog_term_continuous_theta 3 (le_refl 3) s hs
  · exact clog_series_continuous_theta s hs
