  unfold Fk
  rw [Complex.ofReal_tsum]
  rw [tsum_subtype]
  apply tsum_congr
  intro n
  by_cases h : bigOmega n = k
  · have hmem : n ∈ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} := by
      refine ⟨ two_le_of_bigOmega_eq k hk h, h ⟩
    rw [Set.indicator_of_mem hmem, if_pos h]
    push_cast
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_num
  · have hnmem : n ∉ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} := by
      intro hcon
      exact h hcon.2
    rw [Set.indicator_of_notMem hnmem, if_neg h]
    simp
