/-- The derivative of Lemma 3.9's bracket C(s) = z c(s,z).
Sum of the kappa-part, the p = 3 term, and the tail series. -/
theorem hasDerivAt_c_bracket (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) (f fp : ℝ → ℝ)
    (hfp : HasDerivAt f (fp s) s) :
    HasDerivAt (fun t : ℝ =>
        z * (((f t + Real.log 2 / ((2:ℝ) ^ t - 1) : ℝ)) : ℂ)
          + ((-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
              / ((((((3:ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
                / ((((((3:ℕ):ℝ)) ^ t : ℝ) : ℂ) - z))
            + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                  / ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
                    / ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - z))))
      (z * (((fp s + -((Real.log 2) ^ 2 * (2:ℝ) ^ s) / ((2:ℝ) ^ s - 1) ^ 2 : ℝ)) : ℂ)
        + ((z * ((z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) ^ 2
              * (((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ)
              * ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z
                + ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
            / (((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
              * (((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (z * ((z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) ^ 2
                  * (((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)
                  * ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z
                    + ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
                / (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
                  * (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))))) s := by
  have hkp := hasDerivAt_kappa_part z s hsmem f fp hfp
  have hp3 := deriv2_clog_prime_term_z 3 (le_refl 3) s (le_of_lt hsmem.1) z hz
  have htail := hasDerivAt_clog_series2 z hz s hsmem
  exact hkp.add (hp3.add htail)
