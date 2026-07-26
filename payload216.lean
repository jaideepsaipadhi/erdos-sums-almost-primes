/-!
### G2at1 2 = d  (manuscript section 1, second identity)

Numerically verified: both sides are 0.37869502330363.

NOTE this is only the FUNCTION-VALUE half of "sum 2^i c_i = d".  The series
half needs z = 2 inside the disc of analyticity, and G2C_differentiableOn
currently gives ball 0 2 only, so that remains blocked on extending the
radius past 2 (see HANDOFF).

Decomposition:
  D1  per-factor: at z = 2, s = 1 the complex factor is the cast of the real
      factor (1 - 2/p)^(-1) (1 - 1/p)^2.
  D2  the real p >= 3 family is multipliable (same comparison as
      cFac_multipliable, with (1-2/p)^(-1) in place of (1-1/p)^(-1);
      needs p >= 5 or a per-prime check since 1 - 2/3 = 1/3 is small).
  D3  ofReal transfer, as in cFac_ofReal.
  D4  indicator-over-Nat.Primes = subtype-over-{p >= 3}, as in A3.
  D5  combine with the (1/2)^2 = 1/4 prefactor.
-/

/-- D1: at z = 2, s = 1 the regularised factor is the cast of the real one. -/
theorem reg_factor_at_two (y : ℝ) (hy : (1:ℝ) - 2 * y ≠ 0) :
    (1 - (2:ℂ) * ((y : ℝ) : ℂ))⁻¹ * (((1 - y : ℝ)) : ℂ) ^ (2:ℂ)
      = ((((1 - 2*y : ℝ))⁻¹ * ((1 - y : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have hcast2 : ((1 - 2*y : ℝ) : ℂ) = 1 - (2:ℂ) * ((y : ℝ) : ℂ) := by
    push_cast; ring
  have hne : (1:ℂ) - (2:ℂ) * ((y : ℝ) : ℂ) ≠ 0 := by
    rw [← hcast2]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy
  have hpow : (((1 - y : ℝ)) : ℂ) ^ (2:ℂ) = (((1 - y : ℝ)) : ℂ) ^ (2:ℕ) := by
    rw [← Complex.cpow_natCast]
    norm_num
  rw [hpow]
  push_cast
  rw [← hcast2]
  push_cast
  field_simp
