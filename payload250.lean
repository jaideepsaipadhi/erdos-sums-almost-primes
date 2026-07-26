/-- Definition 2.3 read as a formula for A_m in terms of delta_m. -/
theorem Am_eq_delta (m : ℕ) :
    Am m = (2:ℝ) ^ (m + 1) - (Real.log 2 / 4) * (m : ℝ) ^ 2 + deltaM m := by
  unfold deltaM
  ring
