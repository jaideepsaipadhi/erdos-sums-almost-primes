  have hfac : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpull : (∑' n : ℕ,
      (if bigOmega n = k then (Nat.factorial k : ℂ) * (((n:ℂ)) ^ (-(s:ℂ))) else 0))
      = (Nat.factorial k : ℂ) * ∑' n : ℕ,
        (if bigOmega n = k then (((n:ℂ)) ^ (-(s:ℂ))) else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases h : bigOmega n = k
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hpull, mul_div_assoc, div_self hfac, one_mul]
  sorry
