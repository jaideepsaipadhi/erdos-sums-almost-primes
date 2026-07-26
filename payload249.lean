/-- Partial sums of the c_i: manuscript section 2.3's w_k is the tail. -/
theorem cCoeff_partial_sum (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (cCoeff i).re = 1/2 - wk k := by
  unfold wk
  exact sum_range_eq_total_sub_tail cCoeff_re_sum k

/-- Partial sums of 2^i c_i: W_k is the tail. -/
theorem cCoeff_two_pow_partial_sum (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (2:ℝ) ^ i * (cCoeff i).re = dConst - Wk k := by
  unfold Wk
  exact sum_range_eq_total_sub_tail cCoeff_re_two_pow_sum k
