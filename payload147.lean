/-- The regularised family is multipliable over p >= 3: adjoin the single
p = 3 factor to the p >= 5 tail (the p=3 exp-log BOUND fails, but the single
extra factor is harmless). -/
theorem reg_multipliable_three (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
        * (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have h5 := prime_factor_multipliable_complex s hs z hz
  have hsplit := tprod_split_three
    (fun n : ℕ => (1 - z * (((n:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      * (((1 - (n:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) h5
  exact hsplit.1
