/-- The log^2-weighted series is dominated by a p-series, uniformly for s >= 1:
log^2 p * p^(-2s) <= (64/9) p^(3/4 - 2s) <= (64/9) p^(-5/4).
The r=2 analogue of deriv_series_summable. -/
theorem deriv2_series_summable (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (Real.log ((p:ℕ):ℝ)) ^ 2 * (((p:ℕ):ℝ)) ^ (-2*s)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (64/9) * (((p:ℕ):ℝ)) ^ (-(5:ℝ)/4)) := by
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(5:ℝ)/4)) := by
      rw [Real.summable_nat_rpow]
      norm_num
    exact (hbase.subtype _).mul_left (64/9)
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro p
    have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    positivity
  · intro p
    have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
    have hlog := log_sq_le (((p:ℕ):ℝ)) hp3
    have hpos : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-2*s) := Real.rpow_pos_of_pos hp0 _
    have hstep : (Real.log ((p:ℕ):ℝ)) ^ 2 * (((p:ℕ):ℝ)) ^ (-2*s)
        ≤ ((64/9) * (((p:ℕ):ℝ)) ^ ((3:ℝ)/4)) * (((p:ℕ):ℝ)) ^ (-2*s) :=
      mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    have hcomb : ((64/9) * (((p:ℕ):ℝ)) ^ ((3:ℝ)/4)) * (((p:ℕ):ℝ)) ^ (-2*s)
        = (64/9) * (((p:ℕ):ℝ)) ^ ((3:ℝ)/4 + -2*s) := by
      rw [mul_assoc, ← Real.rpow_add hp0]
    have hmono : (((p:ℕ):ℝ)) ^ ((3:ℝ)/4 + -2*s) ≤ (((p:ℕ):ℝ)) ^ (-(5:ℝ)/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [hcomb] at hstep
    nlinarith [hstep, hmono, hpos]
