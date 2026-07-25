/-- The regularised family is multipliable over primes >= 3, from the p >= 5 case. -/
theorem prime_factor_multipliable_three (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
        * (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  sorry
