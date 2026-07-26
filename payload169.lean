/-- Radius version of A1: summability for any ||z|| < 2^s. -/
theorem zOmega_summable_radius (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz2 : Norm.norm z < (2:ℝ) ^ s) :
    Summable (fun n : ℕ => Norm.norm (zOmegaHom s z n)) := by
  sorry
