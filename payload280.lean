/-- Termwise differentiation of the complex p >= 5 log-series.
Complex analogue of hasDerivAt_log_series; hasDerivAt_tsum_of_isPreconnected
takes F in any complete normed space, so C works unchanged. -/
theorem hasDerivAt_clog_series (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ)))
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) s := by
  have hy0 : (3/2 : ℝ) ∈ Set.Ioo (1:ℝ) 2 := by
    constructor <;> norm_num
  apply hasDerivAt_tsum_of_isPreconnected
    deriv_bound_uniform_summable_five isOpen_Ioo isPreconnected_Ioo
    _ _ hy0 (clog_series_summable_at_basepoint z hz) hsmem
  · intro p y hy
    exact deriv_clog_prime_factor_canon (p:ℕ) p.2.2 y (le_of_lt hy.1) z hz
  · intro p y hy
    exact deriv_clog_term_bound_uniform (p:ℕ) (by omega) y (le_of_lt hy.1) z hz
