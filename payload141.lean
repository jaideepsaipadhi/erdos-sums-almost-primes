/-- B3 (HasProd form): the p >= 3 family has the factored value.
Stated with HasProd rather than tprod because HasProd composes with
mul_compl and Equiv.hasProd_iff, which tprod does not. -/
theorem tail_regroup_hasProd (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      (((cFac s : ℝ) : ℂ) ^ z * G2C s z) := by
  sorry
