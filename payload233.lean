/-- Wide-radius variant: the tail product converges for ||z|| <= 5/2. -/
theorem G2tailC_hasProd_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 5/2) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * ((((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ)) : ℂ)) ^ z)
      (G2tailC s z) :=
  (prime_factor_multipliable_complex_wide s hs z hz).hasProd
