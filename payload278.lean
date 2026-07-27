/-- The s-free dominator, indexed over p >= 5 to match G2tailC.
Rebuilt from the N-indexed p-series rather than restricted from the p >= 3
version: those are different subtypes of N, neither contained in the other as
Lean sees it, and the file's idiom (line ~1126) is to restrict from N. -/
theorem deriv_bound_uniform_summable_five :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      27 * Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-(2:ℝ))) := by
  have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(3:ℝ)/2)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (((p:ℕ):ℝ)) ^ (-(3:ℝ)/2)) := hbase.subtype _
  have h27 := hsub.mul_left 27
  apply Summable.of_nonneg_of_le _ _ h27
  · intro p
    have hp5 : (5:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have : (0:ℝ) ≤ Real.log ((p:ℕ):ℝ) := Real.log_nonneg (by linarith)
    positivity
  · intro p
    have hp5 : (5:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
    have hlog := log_le_sqrt (((p:ℕ):ℝ)) (by linarith)
    have hpos : (0:ℝ) < (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hp0 _
    have hstep : Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-(2:ℝ))
        ≤ ((((p:ℕ):ℝ)) ^ ((1:ℝ)/2)) * (((p:ℕ):ℝ)) ^ (-(2:ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    have hcomb : ((((p:ℕ):ℝ)) ^ ((1:ℝ)/2)) * (((p:ℕ):ℝ)) ^ (-(2:ℝ))
        = (((p:ℕ):ℝ)) ^ (-(3:ℝ)/2) := by
      rw [← Real.rpow_add hp0]
      norm_num
    rw [hcomb] at hstep
    nlinarith [hstep]
