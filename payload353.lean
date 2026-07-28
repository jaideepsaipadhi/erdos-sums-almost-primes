/-- The p >= 5 series in cBracket converges at s = 1.
Needed for cBracket f1 1 z to be a genuine value rather than a tsum junk
value: at s = 1 the terms are -z(z-1)log p/((p-1)(p-z)), which is O(log p/p^2). -/
theorem cBracket_series_summable_at_one (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      -(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / ((((((p:ℕ):ℝ)) ^ (1:ℝ) : ℝ) : ℂ) - 1)
          / ((((((p:ℕ):ℝ)) ^ (1:ℝ) : ℝ) : ℂ) - z)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    _ deriv_bound_uniform_summable_five
  intro p
  exact deriv_clog_term_bound_uniform (p:ℕ) (by omega) 1 (le_refl 1) z hz
