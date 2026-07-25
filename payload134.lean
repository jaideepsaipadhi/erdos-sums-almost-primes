/-- A prime p with 3 <= p and p != 3 satisfies 5 <= p (4 is not prime). -/
theorem five_le_of_prime_ne_three {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (hne : p ≠ 3) :
    5 ≤ p := by
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p
    · exact absurd rfl hne
    · exact absurd hp (by norm_num)
  · exact h
