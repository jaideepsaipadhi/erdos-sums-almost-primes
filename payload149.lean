/-- The family (1 - p^-s)^(-z) is multipliable over primes >= 3. -/
theorem cpow_neg_multipliable_three (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z)) := by
  sorry
