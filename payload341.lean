/-- C' is continuous in theta on the contour: the kappa-part is constant in
theta apart from the z factor, the p=3 term is clog2_term_continuous_theta at
p = 3, and the tail is clog2_series_continuous_theta. -/
theorem c_bracket_deriv_continuous_theta (s : ℝ) (hs : 1 ≤ s) (fps : ℝ) :
    Continuous (fun theta : ℝ =>
      circleMap 0 (2:ℝ) theta * (((fps + -((Real.log 2) ^ 2 * (2:ℝ) ^ s)
            / ((2:ℝ) ^ s - 1) ^ 2 : ℝ)) : ℂ)
        + ((circleMap 0 (2:ℝ) theta * ((circleMap 0 (2:ℝ) theta - 1)
              * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ)
              * ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta
                + ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
            / (((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
              * (((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta) ^ 2))))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (circleMap 0 (2:ℝ) theta * ((circleMap 0 (2:ℝ) theta - 1)
                  * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) ^ 2
                  * (((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)
                  * ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2:ℝ) theta
                    + ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
                / (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
                  * (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)
                    - circleMap 0 (2:ℝ) theta) ^ 2)))))) := by
  have hcm : Continuous (circleMap 0 (2:ℝ)) := continuous_circleMap 0 _
  apply Continuous.add (hcm.mul continuous_const)
  apply Continuous.add
  · exact clog2_term_continuous_theta 3 (le_refl 3) s hs
  · exact clog2_series_continuous_theta s hs
