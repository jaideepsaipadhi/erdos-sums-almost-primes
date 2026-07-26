/-- D4: dConst's indicator product over all primes equals the p >= 3 subtype
product, in the spelling G2C and cFac use. -/
theorem dConst_prod_eq_subtype :
    (∏' p : Nat.Primes,
        (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1))
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 := by
  rw [dConst_if_eq_indicator]
  rw [← tprod_subtype {p : Nat.Primes | (3:ℕ) ≤ (p : ℕ)}
    (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)]
  exact (primesEquivSubtypeGE 3).tprod_eq
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)
