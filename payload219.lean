/-- The complex form of the p >= 3 Euler family is multipliable for s > 1,
by mapping the real one through the ofReal ring hom. -/
theorem cFac_multipliable_complex (s : ℝ) (hs : 1 < s) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - (((p:ℕ):ℝ) : ℂ) ^ (-(s:ℂ)))⁻¹) := by
  have hm := cFac_multipliable s hs
  have hmap := hm.map Complex.ofRealHom Complex.continuous_ofReal
  apply hmap.congr
  intro p
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
  show ((((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹ : ℝ)) : ℂ) = _
  push_cast
  congr 1
  rw [Complex.ofReal_cpow (by linarith : (0:ℝ) ≤ ((p:ℕ):ℝ))]
  push_cast
  ring
