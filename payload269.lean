/-- Lemma 3.9's prime part, stated on the product rather than the sum:
d/ds log(prod_{p>=3} regularised factor) = sum_p -z(z-1) log p/((p^s-1)(p^s-z)).
Combines hasDerivAt_log_series with log_reg_tprod_real, transferring the
derivative across the pointwise identity on the open interval. -/
theorem hasDerivAt_log_reg_tprod (z : ℝ) (hz : |z| ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ => Real.log (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * (((p:ℕ):ℝ)) ^ (-t))⁻¹ * (1 - (((p:ℕ):ℝ)) ^ (-t)) ^ z))
      (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-(z * (z - 1) * Real.log ((p:ℕ):ℝ))
          / (((((p:ℕ):ℝ)) ^ s - 1) * ((((p:ℕ):ℝ)) ^ s - z)))) s := by
  have hbase := hasDerivAt_log_series z hz s hsmem
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact log_reg_tprod_real t (le_of_lt ht.1) z hz
