/-- Fbig factors as (A * B) * C in the MANUSCRIPT normalisation:
A = (s-1)^(-z), B = (1 - z/2^s)^(-1), C = G2manu.  Parallel to Fbig_eq_prod,
which uses the cFac normalisation; both expand the same Fbig. -/
theorem Fbig_eq_prod_manu (s : ℝ) (hs : 1 < s) (hc : 0 < cFac s) :
    (fun z : ℂ => Fbig s z)
      = ((fun z : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-z))
          * (fun z : ℂ => (1 - z / ((2:ℂ) ^ (s:ℂ)))⁻¹))
        * (fun z : ℂ => G2manu s z) := by
  funext z
  rw [Fbig_eq_manuscript s hs hc z]
  simp only [Pi.mul_apply]
