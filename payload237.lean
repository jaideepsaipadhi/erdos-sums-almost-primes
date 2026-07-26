/-- Nat.Primes is definitionally {p : N // p.Prime}, but Lean treats the two
spellings as distinct for instance resolution.  This equiv (and the transport
lemma below) let products move between them once, rather than needing a bespoke
equiv at each site. -/
def primesEquivSubtype : Nat.Primes ≃ {p : ℕ // p.Prime} where
  toFun p := ⟨ p.1, p.2 ⟩
  invFun p := ⟨ p.1, p.2 ⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- Restricting the equiv to a threshold condition. -/
def primesEquivSubtypeGE (k : ℕ) :
    {p : Nat.Primes // k ≤ (p : ℕ)} ≃ {p : ℕ // p.Prime ∧ k ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2, q.2 ⟩
  invFun q := ⟨ ⟨ q.1, q.2.1 ⟩, q.2.2 ⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl
