/-- The inner sum of (10) is constant in j: each term is 2^(-(k-i)-1),
so the sum over j <= k-i is (k-i+1) * 2^(-(k-i)-1). -/
theorem inner_sum_const (k i : ℕ) (hik : i ≤ k) (b : ℝ) :
    ∑ j ∈ Finset.range (k - i + 1),
        b * (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ ((k - i - j) + 1))
      = ((k : ℝ) - (i : ℝ) + 1) * (b * (1 / (2:ℝ) ^ ((k - i) + 1))) := by
  have hterm : ∀ j ∈ Finset.range (k - i + 1),
      b * (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ ((k - i - j) + 1))
        = b * (1 / (2:ℝ) ^ ((k - i) + 1)) := by
    intro j hj
    have hjk : j ≤ k - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : (2:ℝ) ^ (-(j:ℝ)) = 1 / (2:ℝ) ^ (j:ℕ) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      ring
    rw [hpow]
    have hsplit : (2:ℝ) ^ ((k - i) + 1) = (2:ℝ) ^ (j:ℕ) * (2:ℝ) ^ ((k - i - j) + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
  rw [nsmul_eq_mul]
  congr 1
  have : ((k - i + 1 : ℕ) : ℝ) = (k : ℝ) - (i : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hik]
    norm_num
  exact this
