/-- Basepoint summability at s = 3/2 over p >= 5, for the complex log-series.
Same shape as prime_factor_sub_one_summable: restrict the N-indexed p-series,
then compare termwise against prime_correction_bound_complex. -/
theorem clog_series_summable_at_basepoint (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      -Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-(3/2:ℝ)) : ℝ) : ℂ))
        + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-(3/2:ℝ))) : ℝ) : ℂ)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      18 * (((p:ℕ):ℝ)) ^ (-2*(3/2:ℝ))) := by
    have h2s : -(2*(3/2:ℝ)) < -1 := by norm_num
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*(3/2:ℝ)))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
        (((p:ℕ):ℝ)) ^ (-(2*(3/2:ℝ)))) := hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (18:ℝ) * (((p:ℕ):ℝ)) ^ (-2*(3/2:ℝ))
          = 18 * (((p:ℕ):ℝ)) ^ (-(2*(3/2:ℝ))) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      prime_correction_bound_complex (p:ℕ) (by omega) (3/2) (by norm_num) z hz)
    hcomp
