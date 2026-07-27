/-- d/ds of kappa(t)^z: the cpow of a positive real function, differentiated
via exp(z log kappa).  Gives kappa^z * z * (log kappa)', and
(log kappa)' = f(s) + log 2/(2^s - 1) by kappaFac_eq_zetaTilde. -/
theorem hasDerivAt_kappa_cpow (z : ℂ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ => ((kappaFac t : ℝ) : ℂ) ^ z)
      (((kappaFac s : ℝ) : ℂ) ^ z
        * (z * (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ))) s := by
  have hs1 : 1 < s := hsmem.1
  have hklog : HasDerivAt (fun t : ℝ => Real.log (kappaFac t))
      (f s + Real.log 2 / ((2:ℝ) ^ s - 1)) s := by
    have hsplit : ∀ t : ℝ, t ∈ Set.Ioo (1:ℝ) 2 →
        Real.log (kappaFac t) = Real.log (zetaTilde t) + Real.log (1 - (2:ℝ) ^ (-t)) := by
      intro t ht
      rw [kappaFac_eq_zetaTilde t ht.1,
        Real.log_mul (ne_of_gt (zetaTilde_pos t ht.1)) (ne_of_gt (one_sub_two_pow_pos t ht.1))]
    have hsum := hf.add (deriv_log_one_sub_two_pow s hs1)
    apply hsum.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
    exact (hsplit t ht).symm
  have hcast : HasDerivAt (fun t : ℝ => ((Real.log (kappaFac t) : ℝ) : ℂ))
      (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ) : ℂ)) s := hklog.ofReal_comp
  have hmul : HasDerivAt (fun t : ℝ => z * ((Real.log (kappaFac t) : ℝ) : ℂ))
      (z * (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)) s := hcast.const_mul z
  have hexp := hmul.cexp
  have heq : ∀ t : ℝ, t ∈ Set.Ioo (1:ℝ) 2 →
      Complex.exp (z * ((Real.log (kappaFac t) : ℝ) : ℂ)) = ((kappaFac t : ℝ) : ℂ) ^ z := by
    intro t ht
    have hkpos : 0 < kappaFac t := kappaFac_pos t ht.1 (cFac_pos t ht.1)
    rw [ofReal_cpow_eq_exp (kappaFac t) hkpos z]
    ring_nf
  rw [← heq s hsmem]
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact (heq t ht).symm
