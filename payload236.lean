/-- D4: dConst's indicator-over-all-primes product equals the p >= 3 subtype
product.  For naturals 2 < p is 3 <= p, so the `if` is exactly the indicator. -/
theorem dConst_prod_eq_subtype :
    (∏' p : Nat.Primes,
        (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1))
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 := by
  sorry
