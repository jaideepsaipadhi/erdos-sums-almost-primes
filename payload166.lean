theorem iteratedDeriv_monomial_zero (m k : ℕ) (c : ℂ) :
    iteratedDeriv k (fun z : ℂ => z ^ m * c) 0
      = if m = k then (Nat.factorial k : ℂ) * c else 0 := by
  have hbase : iteratedDeriv k (fun z : ℂ => z ^ m) 0
      = if m = k then (Nat.factorial k : ℂ) else 0 := by
    rw [iteratedDeriv_pow]
    by_cases h : m = k
    · subst h
      simp [Nat.descFactorial_self]
    · rw [if_neg h]
      rcases Nat.lt_or_ge m k with hlt | hge
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
        simp
      · have hne : m - k ≠ 0 := by omega
        rw [zero_pow hne]
        ring
  have hsplit : (fun z : ℂ => z ^ m * c) = fun z : ℂ => (z ^ m) * c := rfl
  rw [hsplit, iteratedDeriv_mul_const_field, hbase]
  by_cases h : m = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]
