/-- The correction series is continuous in s on {s // 1 <= s}. -/
theorem correction_series_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-(s:ℝ)) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-(s:ℝ))) : ℝ) : ℂ))) := by
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      correction_continuous_s (p:ℕ) (by omega) z hz)
    correction_bound_uniform_summable_five
  intro p s
  exact correction_bound_sfree (p:ℕ) (by omega) (s:ℝ) s.2 z hz
