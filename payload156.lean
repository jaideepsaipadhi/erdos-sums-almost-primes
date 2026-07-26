  have hsumR : HasSum (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)) (Real.log (cFac s)) := by
    have hlogeq : Real.log (cFac s)
        = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
            Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹) := by
      unfold cFac
      exact log_tprod_real hposR hmulR hlogR
    rw [hlogeq]
    exact hlogR.hasSum
  have hsumC : HasSum (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      ((Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹) : ℝ) : ℂ))
      ((Real.log (cFac s) : ℝ) : ℂ) := hsumR.ofReal
  have hbridge := hasProd_cexp_of_hasSum (c := z) hsumC
  rw [cFac_cpow s hc z]
  apply hbridge.congr_fun
  intro p
  have hpos : (0:ℝ) < 1 - ((p:ℕ):ℝ) ^ (-s) := hposR p |> inv_pos.mp
  have hane : (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  rw [Complex.cpow_def_of_ne_zero hane, ←  Complex.ofReal_log hpos.le]
  congr 1
  rw [Real.log_inv]
  push_cast
  ring
