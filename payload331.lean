/-- The z-scaled r=2 per-prime derivative, matching the convention of
lemma_3_9_complex's terms (which carry z(z-1), not (z-1)). -/
theorem deriv2_clog_prime_term_z (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -(z * (z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ))
          / (((((p:ℝ)) ^ t : ℝ) : ℂ) - 1) / (((((p:ℝ)) ^ t : ℝ) : ℂ) - z))
      (z * ((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2 * ((((p:ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))) s := by
  have hbase := (deriv2_clog_prime_term p hp s hs z hz).const_mul z
  apply hbase.congr_of_eventuallyEq
  filter_upwards with t
  field_simp
  ring
