/-- Per-term expansion for the frozen integral, for i <= k. -/
theorem Ikfrozen_term (k i : ℕ) (hi : i ≤ k) :
    (cCoeff i).re * Sm (k - i)
      = 2 * (cCoeff i).re
        - (Real.log 2 / 4) * ((2:ℝ)^i * (cCoeff i).re * ((k:ℝ) - (i:ℝ))^2) / (2:ℝ)^k
        + ((2:ℝ)^i * (cCoeff i).re * deltaM (k - i)) / (2:ℝ)^k := by
  have hpow : (2:ℝ)^(k-i) * (2:ℝ)^i = (2:ℝ)^k := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have hcast : ((k - i : ℕ) : ℝ) = (k:ℝ) - (i:ℝ) := Nat.cast_sub hi
  have h1 : ((2:ℝ)^(k-i)) ≠ 0 := by positivity
  have h2 : ((2:ℝ)^i) ≠ 0 := by positivity
  rw [Sm_eq_Am_div, Am_eq_delta, hcast, ← hpow]
  field_simp
  ring
