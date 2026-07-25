/-- Summability of the correction for the (1 - p^-s)^(-z) family, p >= 5. -/
theorem cpow_neg_sub_one_summable (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      Norm.norm ((((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z) - 1)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 8 * (((p:ℕ):ℝ) ^ (-s))) := by
    have hbase : Summable (fun n : ℕ => ((n:ℝ) ^ (-s))) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => (((p:ℕ):ℝ) ^ (-s))) :=
      hbase.subtype _
    exact hsub.mul_left 8
  apply Summable.of_nonneg_of_le
    (fun p => norm_nonneg _)
    (fun p => cpow_neg_sub_one_bound (p:ℕ) p.property.2 s hs z hz)
    hcomp
