/-- d/ds G2tailC = G2tailC * (sum of per-prime derivatives).
The key step of the complex chain: G2tailC is exp of the log-series
(G2tailC_eq_exp_sum), so differentiating goes through HasDerivAt.cexp and
never requires Complex.log of the product -- which would be false in general
because of branch cuts. -/
theorem hasDerivAt_G2tailC (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ => G2tailC t z)
      (G2tailC s z * ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) s := by
  have hser := hasDerivAt_clog_series z hz s hsmem
  have hexp := hser.cexp
  have heq : ∀ t : ℝ, t ∈ Set.Ioo (1:ℝ) 2 →
      Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ)))
      = G2tailC t z := by
    intro t ht
    exact (G2tailC_eq_exp_sum t (le_of_lt ht.1) z hz).symm
  have hval : Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-s)) : ℝ) : ℂ)))
      = G2tailC s z := heq s hsmem
  rw [← hval]
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact (heq t ht).symm
