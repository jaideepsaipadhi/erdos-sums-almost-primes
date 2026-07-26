/-- The cpow-negative product equals cFac^z. Bridges the complex product to
the real log-sum via reg_factors_tprod. -/
theorem cpow_neg_tprod_eq_cFac (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z))
      (((cFac s : ℝ) : ℂ) ^ z) := by
  sorry
