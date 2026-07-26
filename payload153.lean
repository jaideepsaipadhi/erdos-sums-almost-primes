/-- Pointwise factorisation: the plain Euler factor splits into the
cpow-negative factor times the regularised factor. -/
theorem euler_factor_split (a : ℝ) (ha : 0 < 1 - a) (z w : ℂ) :
    (1 - w)⁻¹ = ((((1 - a : ℝ)) : ℂ)) ^ (-z)
      * ((1 - w)⁻¹ * (((1 - a : ℝ)) : ℂ) ^ z) := by
  have hane : (((1 - a : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  rw [Complex.cpow_neg]
  field_simp
