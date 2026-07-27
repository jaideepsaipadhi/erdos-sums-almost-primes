/-- The per-prime derivative sum is continuous in theta on the contour.
continuous_tsum needs a GLOBAL bound (all theta), which holds here precisely
because circleMap always lands on |z| = 2, where
deriv_clog_term_bound_uniform applies. -/
theorem clog_series_continuous_theta (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(circleMap 0 (2:ℝ) theta * (circleMap 0 (2:ℝ) theta - 1)
            * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2:ℝ) theta))) := by
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2:ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      clog_term_continuous_theta (p:ℕ) (by omega) s hs)
    deriv_bound_uniform_summable_five
  intro p theta
  exact deriv_clog_term_bound_uniform (p:ℕ) (by omega) s hs
    (circleMap 0 (2:ℝ) theta) (hnorm theta)
