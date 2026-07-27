/-- File-canonical form of the complex per-prime derivative: second term as a
real log cast to C (matching G2tailC_eq_exp_sum and
prime_correction_summable_complex), indexed from p >= 5 to match G2tailC. -/
theorem deriv_clog_prime_factor_canon (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ))
      (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)) s := by
  have hp3 : (3:ℕ) ≤ p := by omega
  have hbase := deriv_clog_prime_factor p hp3 s hs z hz
  apply hbase.congr_of_eventuallyEq
  have hnhds : Set.Ioi (0:ℝ) ∈ nhds s := by
    apply Ioi_mem_nhds
    linarith
  filter_upwards [hnhds] with t ht
  congr 1
  congr 1
  have hpr : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp3
  have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
  have hlt : (((p:ℕ):ℝ)) ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith [ht])
  have hpos : (0:ℝ) < 1 - (((p:ℕ):ℝ)) ^ (-t) := by linarith
  rw [Complex.ofReal_log (le_of_lt hpos)]
  push_cast
  ring
