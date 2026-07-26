/-- For a positive real base, cpow is exp of the real log. -/
theorem ofReal_cpow_eq_exp (a : ℝ) (ha : 0 < a) (w : ℂ) :
    ((a : ℝ) : ℂ) ^ w = Complex.exp (w * ((Real.log a : ℝ) : ℂ)) := by
  have hne : ((a : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt ha
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  rw [← Complex.ofReal_log (le_of_lt ha)]
  ring

/-- The manuscript's decomposition: Fbig = (s-1)^(-z) (1 - z/2^s)^(-1) G2manu.
This is the same F as our cFac form, resplit so that the z-power of the first
factor contributes (-log(s-1))^l / l! -- the form Definition 2.3 consumes. -/
theorem Fbig_eq_manuscript (s : ℝ) (hs : 1 < s) (hc : 0 < cFac s) (z : ℂ) :
    Fbig s z = ((s - 1 : ℝ) : ℂ) ^ (-z) * (1 - z / ((2:ℂ) ^ (s:ℂ)))⁻¹ * G2manu s z := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hk : (0:ℝ) < kappaFac s := kappaFac_pos s hs hc
  unfold Fbig G2manu
  rw [ofReal_cpow_eq_exp (cFac s) hc z, ofReal_cpow_eq_exp (s - 1) hs1 (-z),
    ofReal_cpow_eq_exp (kappaFac s) hk z]
  have hlog : Real.log (kappaFac s) = Real.log (s - 1) + Real.log (cFac s) := by
    unfold kappaFac
    rw [Real.log_mul (ne_of_gt hs1) (ne_of_gt hc)]
  rw [hlog]
  push_cast
  rw [← Complex.exp_add]
  ring_nf
