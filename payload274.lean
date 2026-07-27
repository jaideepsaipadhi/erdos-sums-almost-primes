/-- Complex analogue of deriv_log_one_sub_const_rpow:
d/ds Complex.log(1 - c*p^(-s)) = c*log p*p^(-s)/(1 - c*p^(-s)) for complex c.
The inner function is real-valued (the exponent is real), so its derivative
comes from hasDerivAt_rpow_neg cast to C; only the outer log is complex, and
one_sub_mem_slitPlane supplies its side condition. -/
theorem deriv_clog_one_sub_const_rpow (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (c : ℂ) (hc : Norm.norm c ≤ 2) :
    HasDerivAt (fun t : ℝ => Complex.log (1 - c * (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)))
      (c * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) * ((((((p:ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
        / (1 - c * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))) s := by
  have hslit := one_sub_mem_slitPlane p hp s hs c hc
  have hreal := hasDerivAt_rpow_neg p hp s
  have hcast : HasDerivAt (fun t : ℝ => (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
      (((-((((p:ℕ):ℝ)) ^ (-s) * Real.log ((p:ℕ):ℝ)) : ℝ) : ℂ)) s :=
    hreal.ofReal_comp
  have hin : HasDerivAt (fun t : ℝ => 1 - c * (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
      (c * (((((((p:ℕ):ℝ)) ^ (-s) * Real.log ((p:ℕ):ℝ)) : ℝ)) : ℂ)) s := by
    have h := (hcast.const_mul c).const_sub 1
    have hval : c * (((((((p:ℕ):ℝ)) ^ (-s) * Real.log ((p:ℕ):ℝ)) : ℝ)) : ℂ)
        = -(c * ((-((((p:ℕ):ℝ)) ^ (-s) * Real.log ((p:ℕ):ℝ)) : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hval]
    exact h
  have h := (Complex.hasDerivAt_log hslit).scomp s hin
  simp only [Function.comp_def, smul_eq_mul] at h
  have hne : (1 : ℂ) - c * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ) ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  have hval : c * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ)
        * ((((((p:ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
        / (1 - c * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))
      = c * (((((((p:ℕ):ℝ)) ^ (-s) * Real.log ((p:ℕ):ℝ)) : ℝ)) : ℂ)
        * (1 - c * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    push_cast
    field_simp
    ring
  rw [hval]
  exact h
