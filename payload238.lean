/-- The `if 2 < p` in dConst is the indicator of {p >= 3} (for primes). -/
theorem dConst_if_eq_indicator :
    (fun p : Nat.Primes =>
        (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1))
      = Set.mulIndicator {p : Nat.Primes | (3:ℕ) ≤ (p : ℕ)}
          (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2) := by
  funext p
  by_cases h : (3:ℕ) ≤ (p : ℕ)
  · rw [Set.mulIndicator_of_mem h, if_pos (by omega)]
  · rw [Set.mulIndicator_of_notMem h, if_neg (by omega)]
