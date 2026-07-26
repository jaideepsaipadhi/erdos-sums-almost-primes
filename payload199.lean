/-- A positive real base to a complex power is ContDiff of all orders. -/
theorem contDiffAt_ofReal_cpow (a : ℝ) (ha : 0 < a) (k : ℕ) (z : ℂ) :
    ContDiffAt ℂ k (fun w : ℂ => ((a : ℝ) : ℂ) ^ w) z := by
  have hrewrite : (fun w : ℂ => ((a : ℝ) : ℂ) ^ w)
      = fun w : ℂ => Complex.exp (w * ((Real.log a : ℝ) : ℂ)) := by
    funext w
    exact ofReal_cpow_eq_exp a ha w
  rw [hrewrite]
  apply ContDiff.contDiffAt
  apply ContDiff.cexp
  exact contDiff_id.mul contDiff_const

/-- Factor C in the manuscript decomposition: G2manu is ContDiff of all orders. -/
theorem contDiffAt_factorCmanu (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (k : ℕ) :
    ContDiffAt ℂ k (fun w : ℂ => G2manu s w) 0 := by
  have heq : (fun w : ℂ => G2manu s w)
      = (fun w : ℂ => ((kappaFac s : ℝ) : ℂ) ^ w) * (fun w : ℂ => G2C s w) := by
    funext w
    unfold G2manu
    simp only [Pi.mul_apply]
  rw [heq]
  exact (contDiffAt_ofReal_cpow (kappaFac s) hk k 0).mul (contDiffAt_factorC s hs k)
