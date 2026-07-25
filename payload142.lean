/-- The regularising factors, as a product, give cFac^z.
This is the cpow-of-tprod step, routed through B1 (log_tprod_real). -/
theorem reg_factors_tprod (s : ℝ) (hs : 1 ≤ s) (z : ℂ)
    (hmul : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))
    (hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)
    (hlog : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))) :
    ((cFac s : ℝ) : ℂ) ^ z
      = Complex.exp (z * ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          ((Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹) : ℝ) : ℂ)) := by
  sorry
