/-- The regularised factor collapses at z = 1. -/
theorem reg_factor_at_one (y : ℝ) (hy : (1:ℝ) - y ≠ 0) :
    (1 - (1:ℂ) * ((y : ℝ) : ℂ))⁻¹ * (((1 - y : ℝ)) : ℂ) ^ (1:ℂ) = 1 := by
  rw [one_mul, Complex.cpow_one]
  have hcast : ((1 - y : ℝ) : ℂ) = 1 - ((y : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  have hne : (1 : ℂ) - ((y : ℝ) : ℂ) ≠ 0 := by
    rw [← hcast]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy
  field_simp
