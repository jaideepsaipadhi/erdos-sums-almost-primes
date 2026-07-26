/-- Summability of the derivative bound family. -/
theorem deriv_bound_summable (s : ℝ) (hs : 1 < s) (j : ℕ)
    (r0 r : ℝ) (hr01 : 1 ≤ r0) (hr0r : r0 < r)
    (hr0 : 0 ≤ r) (hr3 : r * ((3:ℝ) ^ (-s)) ≤ 1/2) (hr2 : r < (2:ℝ) ^ s) :
    Summable (fun n : ℕ =>
      ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n - j) * ((n:ℝ) ^ (-s))) := by
  have hbase := omega_pow_summable_radius s hs j r0 r (by linarith) hr0r hr0 hr3 hr2
  apply Summable.of_nonneg_of_le _ _ hbase
  · intro n
    positivity
  · intro n
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_right_of_le_one_or_le hr01
    exact Nat.sub_le _ _
