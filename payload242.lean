/-- The complex product of casts at z = 2 is the cast of the real product. -/
theorem dConst_prod_ofReal :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        ((((1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ))
      = (((∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
  exact (dConst_family_multipliable.map_tprod Complex.ofRealHom Complex.continuous_ofReal).symm
