/-- The complement of {b3} in the p >= 3 primes is equivalent to the p >= 5 primes. -/
def compl_b3_equiv :
    (({⟨ 3, Nat.prime_three, le_refl 3 ⟩} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ :
      Set {p : ℕ // p.Prime ∧ 3 ≤ p}) ≃ {p : ℕ // p.Prime ∧ 5 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2.1, by
    have hne : q.1.1 ≠ 3 := by
      intro h
      apply q.2
      apply Subtype.ext
      exact h
    exact five_le_of_prime_ne_three q.1.2.1 q.1.2.2 hne ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1, by have := r.2.2; omega ⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h5 := r.2.2
    have : r.1 = 3 := congrArg Subtype.val h
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
