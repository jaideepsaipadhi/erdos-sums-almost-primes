/-- The norm of the z-weighted family, bundled as a real monoid-with-zero hom. -/
noncomputable def zOmegaNormHom (s : ℝ) (z : ℂ) : ℕ →*₀ ℝ where
  toFun n := Norm.norm (zOmegaHom s z n)
  map_zero' := by
    simp only [map_zero, norm_zero]
  map_one' := by
    simp only [map_one, norm_one]
  map_mul' := by
    intro a b
    simp only [map_mul, norm_mul]

/-- The norm bundle agrees with the norm of the complex bundle. -/
theorem zOmegaNormHom_apply (s : ℝ) (z : ℂ) (n : ℕ) :
    zOmegaNormHom s z n = Norm.norm (zOmegaHom s z n) := rfl
