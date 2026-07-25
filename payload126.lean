    have hGnn : ∀ i : ℕ, (0:ℝ) ≤ G i := fun i => le_trans zero_le_one (hGone i)
    by_cases hN2 : 2 ∈ Finset.range N
    · rw [←  Finset.mul_prod_erase (Finset.range N) G hN2]
      have hG2 : G 2 = (1 - Norm.norm z * ((2:ℝ) ^ (-s)))⁻¹ := by
        rw [hG, Set.mulIndicator_of_mem]
        · norm_num
        · exact Nat.prime_two
      rw [hG2]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (by rw [←  hG2]; exact hGone 2))
      sorry
    · sorry
