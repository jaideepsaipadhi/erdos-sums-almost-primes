theorem Ikfrozen_re_expand (k : ℕ) :
    (Ikfrozen k).re
      = 2 * (1/2 - wk k)
        - (Real.log 2 / 4)
            * ((k:ℝ)^2 * (dConst - Wk k) - 2 * (k:ℝ) * Uk k + Vk k) / (2:ℝ) ^ k
        + DeltaConv k / (2:ℝ) ^ k := by
  rw [Ikfrozen_re_eq]
  rw [Finset.sum_congr rfl (fun i hi => Ikfrozen_term k i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · rw [← Finset.mul_sum, cCoeff_partial_sum]
    · rw [← Finset.sum_div, ← Finset.mul_sum]
      congr 2
      exact sum_two_pow_sq_expand k
  · rw [← Finset.sum_div]
    unfold DeltaConv
    apply Finset.sum_congr rfl
    intro i _
    ring
