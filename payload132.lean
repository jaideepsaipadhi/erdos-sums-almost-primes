theorem cFac_cpow (s : ℝ) (hc : 0 < cFac s) (z : ℂ) :
    ((cFac s : ℝ) : ℂ) ^ z
      = Complex.exp (z * ((Real.log (cFac s) : ℝ) : ℂ)) := by
  have hne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hc
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  rw [←  Complex.ofReal_log (le_of_lt hc)]
  ring
