/-- The r=2 s-free dominator, indexed at p >= 5.
Rebuilt from the N-indexed p-series rather than restricted from the p >= 3
version, per the file's idiom. -/
theorem deriv2_bound_uniform_summable_five :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      200 * (Real.log ((p:ℕ):ℝ)) ^ 2 * (((p:ℕ):ℝ)) ^ (-(2:ℝ))) := by
  have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(5:ℝ)/4)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (((p:ℕ):ℝ)) ^ (-(5:ℝ)/4)) := hbase.subtype _
  have hc := hsub.mul_left ((200:ℝ) * (64/9))
  apply Summable.of_nonneg_of_le _ _ hc
  · intro p
    have hp5 : (5:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have : (0:ℝ) ≤ (Real.log ((p:ℕ):ℝ)) ^ 2 := sq_nonneg _
    positivity
  · intro p
    have hp5 : (5:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
    have hlog := log_sq_le (((p:ℕ):ℝ)) (by linarith)
    have hpos : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hp0 _
    have hstep : (Real.log ((p:ℕ):ℝ)) ^ 2 * (((p:ℕ):ℝ)) ^ (-(2:ℝ))
        ≤ ((64/9) * (((p:ℕ):ℝ)) ^ ((3:ℝ)/4)) * (((p:ℕ):ℝ)) ^ (-(2:ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    have hcomb : ((64/9) * (((p:ℕ):ℝ)) ^ ((3:ℝ)/4)) * (((p:ℕ):ℝ)) ^ (-(2:ℝ))
        = (64/9) * (((p:ℕ):ℝ)) ^ ((3:ℝ)/4 + -(2:ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hp0]
    have hmono : (((p:ℕ):ℝ)) ^ ((3:ℝ)/4 + -(2:ℝ)) ≤ (((p:ℕ):ℝ)) ^ (-(5:ℝ)/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      norm_num
    rw [hcomb] at hstep
    nlinarith [hstep, hmono, hpos, sq_nonneg (Real.log ((p:ℕ):ℝ))]
