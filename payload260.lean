/-- The differentiated log-series is dominated by a p-series, uniformly for
s >= 1: log p * p^(-2s) <= p^(1/2 - 2s) <= p^(-3/2).
This is the estimate behind both Lemma 3.8's "product converging locally
uniformly" and Lemma 3.9's termwise differentiation. -/
theorem deriv_series_summable (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-2*s)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (((p:ℕ):ℝ)) ^ (-(3:ℝ)/2) := by
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(3:ℝ)/2)) := by
      rw [Real.summable_nat_rpow]
      norm_num
    exact hbase.subtype _
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro p
    have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
    have hlog : (0:ℝ) ≤ Real.log ((p:ℕ):ℝ) := Real.log_nonneg (by linarith)
    positivity
  · intro p
    have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by linarith
    have hlog := log_le_sqrt ((p:ℕ):ℝ) hp3
    have hstep : Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-2*s)
        ≤ (((p:ℕ):ℝ)) ^ ((1:ℝ)/2) * (((p:ℕ):ℝ)) ^ (-2*s) := by
      apply mul_le_mul_of_nonneg_right hlog (by positivity)
    have hcomb : (((p:ℕ):ℝ)) ^ ((1:ℝ)/2) * (((p:ℕ):ℝ)) ^ (-2*s)
        = (((p:ℕ):ℝ)) ^ ((1:ℝ)/2 - 2*s) := by
      rw [← Real.rpow_add hp0]
      ring_nf
    have hmono : (((p:ℕ):ℝ)) ^ ((1:ℝ)/2 - 2*s) ≤ (((p:ℕ):ℝ)) ^ (-(3:ℝ)/2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [hcomb] at hstep
    linarith
