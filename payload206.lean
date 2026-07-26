/-- Each cFac factor is positive, and its argument is at most 1/3, for s > 1. -/
theorem cFac_factor_le_third (s : ℝ) (hs : 1 < s) (p : {p : ℕ // p.Prime ∧ 3 ≤ p}) :
    ((p:ℕ):ℝ) ^ (-s) ≤ 1/3 ∧ 0 < ((p:ℕ):ℝ) ^ (-s) := by
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
  constructor
  · have h1 : ((p:ℕ):ℝ) ^ (-s) ≤ ((p:ℕ):ℝ) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : (((p:ℕ):ℝ))⁻¹ ≤ 1/3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  · positivity

/-- The logs of the cFac factors are summable: -log(1-x) <= 2x for x <= 1/2,
and x = p^(-s) is p-series summable. -/
theorem cFac_log_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      2 * (((p:ℕ):ℝ) ^ (-s))) := by
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-s)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (hbase.subtype _).mul_left _
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro p
    obtain ⟨ h3, hp ⟩ := cFac_factor_le_third s hs p
    apply Real.log_nonneg
    rw [le_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  · intro p
    obtain ⟨ h3, hp ⟩ := cFac_factor_le_third s hs p
    rw [Real.log_inv]
    have hkey := neg_log_one_sub_le (((p:ℕ):ℝ) ^ (-s)) (le_of_lt hp) (by linarith)
    linarith
