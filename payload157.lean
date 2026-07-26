/-- The regularised product over p >= 3 is exactly G2C. -/
theorem reg_tprod_eq_G2C (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
          * (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ z)
      = G2C s z := by
  have h5 := prime_factor_multipliable_complex s hs z hz
  have hsplit := tprod_split_three
    (fun n : ℕ => (1 - z * (((n:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      * (((1 - (n:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) h5
  rw [hsplit.2]
  unfold G2C G2tailC
  norm_num
