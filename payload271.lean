/-- MANUSCRIPT LEMMA 3.9, real-z case.  With G2 = kappa^z * (regularised
p >= 3 product), log G2 = z log kappa + log(product), and
  d/ds [that] = z * (log 2/(2^s-1) + f(s) - sum_p (z-1) log p/((p^s-1)(p^s-z))).
f is a hypothesis, not derived: the manuscript certifies it numerically from
FLINT Stieltjes constants rather than expanding it.

SCOPE: real z only.  Section 3.5's beta_i and section 6.1's gammahat_i extract
[z^i] coefficients and need the COMPLEX analogue -- the same chain over C,
where Complex.log's branch cuts make the per-factor step harder than a
transcription.  This real case validates the architecture; it does not
discharge 3.5 or 6.1. -/
theorem lemma_3_9_real (z : ℝ) (hz : |z| ≤ 2) (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ =>
        z * (Real.log (zetaTilde t) + Real.log (1 - (2:ℝ) ^ (-t)))
          + Real.log (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
              (1 - z * (((p:ℕ):ℝ)) ^ (-t))⁻¹ * (1 - (((p:ℕ):ℝ)) ^ (-t)) ^ z))
      (z * (f s + Real.log 2 / ((2:ℝ) ^ s - 1))
        + ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
            (-(z * (z - 1) * Real.log ((p:ℕ):ℝ))
              / (((((p:ℕ):ℝ)) ^ s - 1) * ((((p:ℕ):ℝ)) ^ s - z)))) s := by
  have hs1 : 1 < s := hsmem.1
  have hkap := hf.add (deriv_log_one_sub_two_pow s hs1)
  have hprod := hasDerivAt_log_reg_tprod z hz s hsmem
  exact (hkap.const_mul z).add hprod
