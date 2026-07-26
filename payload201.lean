/-- Factor A in the manuscript normalisation: (s-1)^(-z) is ContDiff of all orders. -/
theorem contDiffAt_factorAmanu (s : ℝ) (hs1 : 0 < s - 1) (k : ℕ) (z : ℂ) :
    ContDiffAt ℂ k (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) z := by
  have hrewrite : (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w))
      = fun w : ℂ => Complex.exp ((-w) * ((Real.log (s - 1) : ℝ) : ℂ)) := by
    funext w
    exact ofReal_cpow_eq_exp (s - 1) hs1 (-w)
  rw [hrewrite]
  apply ContDiff.contDiffAt
  apply ContDiff.cexp
  exact (contDiff_id.neg).mul contDiff_const
