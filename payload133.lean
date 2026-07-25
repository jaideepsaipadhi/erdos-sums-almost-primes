/-- G2C as a single product over p >= 3 (rather than p=3 split off from p>=5). -/
theorem G2C_eq_tprod_three (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    G2C s z = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
        * (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ z := by
  sorry
