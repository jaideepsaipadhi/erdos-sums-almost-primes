/-- c(s) = prod_{p >= 3} (1 - p^(-s))^(-1) = zeta(s)(1 - 2^(-s)).
This is the constant whose z-th power is the first factor of F(s,z)
when G2 is normalised as our G2C (product over p >= 3 of the
regularised factors). -/
noncomputable def cFac (s : ℝ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (1 - (p:ℝ) ^ (-s))⁻¹

/-- Coefficients of the factor c^z: the l-th is (log c)^l / l!. -/
theorem coeff_cpow (s : ℝ) (hc : 0 < cFac s) (l : ℕ) :
    (iteratedDeriv l (fun z : ℂ => ((cFac s : ℝ) : ℂ) ^ z) 0) / (Nat.factorial l : ℂ)
      = (((Real.log (cFac s)) ^ l / (Nat.factorial l) : ℝ) : ℂ) := by
  have hcne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hc
  have hrewrite : (fun z : ℂ => ((cFac s : ℝ) : ℂ) ^ z)
      = fun z : ℂ => Complex.exp (((Real.log (cFac s) : ℝ) : ℂ) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hcne]
    congr 1
    rw [LAℝ Complex.ofReal_log (le_of_lt hc)]
    ring
  rw [hrewrite, iteratedDeriv_cexp_const_mul l ((Real.log (cFac s) : ℝ) : ℂ)]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  push_cast
  ring
