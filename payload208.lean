/-- The real cFac product, cast to C, is the complex product over p >= 3. -/
theorem cFac_ofReal (s : ℝ) (hs : 1 < s) :
    ((cFac s : ℝ) : ℂ)
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - (((p:ℕ):ℝ) : ℂ) ^ (-(s:ℂ)))⁻¹ := by
  have hm := cFac_multipliable s hs
  unfold cFac
  rw [hm.map_tprod Complex.ofRealHom Complex.continuous_ofReal]
  apply tprod_congr
  intro p
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
  have h3 := (cFac_factor_le_third s hs p).1
  have hden : (0:ℝ) < 1 - ((p:ℕ):ℝ) ^ (-s) := by linarith
  push_cast
  congr 1
  rw [show (-(s:ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cpow (by linarith : (0:ℝ) ≤ ((p:ℕ):ℝ))]
  push_cast
  ring
