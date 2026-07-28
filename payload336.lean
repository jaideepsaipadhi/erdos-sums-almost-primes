/-- d/ds of the kappa-part of c, given f' as a hypothesis.
f' is assumed for the same reason f is: the manuscript certifies
f = (log zeta(s)(s-1))' numerically from Stieltjes constants, so its
derivative is certified the same way rather than derived. -/
theorem hasDerivAt_kappa_part (z : ℂ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f fp : ℝ → ℝ)
    (hfp : HasDerivAt f (fp s) s) :
    HasDerivAt (fun t : ℝ =>
        z * (((f t + Real.log 2 / ((2:ℝ) ^ t - 1) : ℝ)) : ℂ))
      (z * (((fp s + -((Real.log 2) ^ 2 * (2:ℝ) ^ s) / ((2:ℝ) ^ s - 1) ^ 2 : ℝ)) : ℂ)) s := by
  have hs1 : 1 < s := hsmem.1
  have hsum := hfp.add (deriv_two_pow_term s hs1)
  have hcast := hsum.ofReal_comp
  exact hcast.const_mul z
