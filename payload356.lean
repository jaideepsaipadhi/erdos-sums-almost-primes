/-- cBracket's series is s-continuous on {s // 1 <= s}. -/
theorem cBracket_series_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ) - 1)
            / (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ) - z))) := by
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      cBracket_term_continuous_s (p:ℕ) (by omega) z hz)
    deriv_bound_uniform_summable_five
  intro p s
  exact deriv_clog_term_bound_uniform (p:ℕ) (by omega) (s:ℝ) s.2 z hz
