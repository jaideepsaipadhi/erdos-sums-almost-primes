/-- The Fk family is summable (real form). -/
theorem Fk_summable_subtype (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} => ((n:ℕ):ℝ) ^ (-s)) := by
  have hbase : Summable (fun n : ℕ => ((n:ℝ) ^ (-s))) := by
    rw [Real.summable_nat_rpow]
    linarith
  exact hbase.subtype _
