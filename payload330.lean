/-- Basepoint summability at s = 3/2 for the r=2 series. -/
theorem deriv2_series_summable_at_basepoint (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      -((z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / ((((((p:ℕ):ℝ)) ^ (3/2:ℝ) : ℝ) : ℂ) - 1)
        / ((((((p:ℕ):ℝ)) ^ (3/2:ℝ) : ℝ) : ℂ) - z)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    _ (deriv_bound_uniform_summable_five)
  intro p
  exact deriv_clog_term_bound_uniform (p:ℕ) (by omega) (3/2) (by norm_num) z hz
