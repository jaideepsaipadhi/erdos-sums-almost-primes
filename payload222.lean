/-- cFac s = zeta(s) * (1 - 2^(-s)) for s > 1. -/
theorem cFac_eq_zeta (s : ℝ) (hs : 1 < s) :
    ((cFac s : ℝ) : ℂ)
      = riemannZeta (s : ℂ) * (1 - ((2:ℂ)) ^ (-(s:ℂ))) := by
  have hzeta := zeta_split_probe s hs
  have hsplit := (tprod_split_two
    (fun n : ℕ => (1 - (((n:ℕ):ℝ) : ℂ) ^ (-(s:ℂ)))⁻¹)
    (cFac_multipliable_complex s hs)).2
  rw [hzeta, cFac_ofReal s hs] at hsplit
  have hcast : (((2:ℕ):ℝ) : ℂ) = ((2:ℂ)) := by norm_num
  rw [hcast] at hsplit
  have hne := two_factor_ne_one s hs
  rw [hsplit]
  field_simp
