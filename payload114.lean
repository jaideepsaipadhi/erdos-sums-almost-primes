/-- The Euler factors as an indicator family on all naturals, multipliable. -/
theorem zOmegaNorm_indicator_multipliable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) :
    Multipliable (Set.mulIndicator {p : ℕ | p.Prime}
      (fun p : ℕ => (1 - Norm.norm z * ((p:ℝ) ^ (-s)))⁻¹)) := by
  rw [← multipliable_subtype_iff_mulIndicator]
  exact zOmega_factors_multipliable s hs z hz
