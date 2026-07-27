/-- d/ds of the p = 3 Euler factor, via exp of its log.
Same route as hasDerivAt_G2tailC applied to a single term:
prime_factor_eq_exp_complex expresses the factor as exp(correction), and
deriv_clog_prime_factor_canon (now at p >= 3) differentiates the exponent. -/
theorem hasDerivAt_prime_three_factor (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ =>
        (1 - z * ((((3:ℝ)) ^ (-t) : ℝ) : ℂ))⁻¹ * (((1 - ((3:ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z)
      (((1 - z * ((((3:ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - ((3:ℝ)) ^ (-s) : ℝ) : ℂ)) ^ z)
        * (-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
            / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
              / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) s := by
  have hder := deriv_clog_prime_factor_canon 3 (le_refl 3) s (le_of_lt hsmem.1) z hz
  have hexp := hder.cexp
  have heq : ∀ t : ℝ, t ∈ Set.Ioo (1:ℝ) 2 →
      Complex.exp (-Complex.log (1 - z * ((((((3:ℕ):ℝ)) ^ (-t) : ℝ)) : ℂ))
          + z * ((Real.log (1 - (((3:ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ))
        = (1 - z * ((((((3:ℕ):ℝ)) ^ (-t) : ℝ)) : ℂ))⁻¹
            * (((1 - (((3:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z := by
    intro t ht
    exact (prime_factor_eq_exp_complex 3 (le_refl 3) t (le_of_lt ht.1) z hz).symm
  rw [← heq s hsmem]
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact (heq t ht).symm
