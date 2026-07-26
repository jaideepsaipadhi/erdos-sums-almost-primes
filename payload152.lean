theorem cpow_neg_multipliable_five (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z)) := by
  have hsum := cpow_neg_sub_one_summable s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + ((((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z) - 1)) := by
    apply Complex.multipliable_one_add_of_summable
    exact hsum.of_norm
  apply hmult.congr
  intro p
  ring
