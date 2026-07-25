theorem reg_factors_tprod (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hc : 0 < cFac s)
    (hmul : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))
    (hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)
    (hlog : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))) :
    ((cFac s : ℝ) : ℂ) ^ z
      = Complex.exp (z * ((∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹) : ℝ) : ℂ)) := by
  rw [cFac_cpow s hc z]
  congr 2
  have hlogeq : Real.log (cFac s)
      = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹) := by
    unfold cFac
    exact log_tprod_real hpos hmul hlog
  rw [hlogeq]
