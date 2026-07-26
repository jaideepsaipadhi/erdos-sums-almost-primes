/-- A prime p with p != 2 satisfies 3 <= p. -/
theorem three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- The complement of {2} in the primes corresponds to the primes >= 3. -/
def compl_two_equiv :
    (({⟨ 2, Nat.prime_two ⟩} : Set Nat.Primes)ᶜ : Set Nat.Primes)
      ≃ {p : ℕ // p.Prime ∧ 3 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2, by
    have hne : q.1.1 ≠ 2 := by
      intro h
      apply q.2
      apply Subtype.ext
      exact h
    exact three_le_of_prime_ne_two q.1.2 hne ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1 ⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h3 := r.2.2
    have : r.1 = 2 := congrArg Subtype.val h
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
