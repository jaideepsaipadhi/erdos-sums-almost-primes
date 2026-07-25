/-- Primes >= 3 excluding 3 correspond to primes >= 5. -/
def primesGE3_ne_equiv :
    {q : {p : ℕ // p.Prime ∧ 3 ≤ p} // q.1 ≠ 3} ≃ {p : ℕ // p.Prime ∧ 5 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2.1,
    five_le_of_prime_ne_three q.1.2.1 q.1.2.2 q.2 ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1, by have h5 := r.2.2; omega ⟩, by
    have h5 := r.2.2
    simp only [ne_eq]
    omega ⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl
