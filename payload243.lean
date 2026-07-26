/-- D5 (manuscript section 1): G2(1,2) = d.
Function-value half of "sum 2^i c_i = d". -/
theorem G2at1_two_eq_dConst : G2at1 2 = ((dConst : ℝ) : ℂ) := by
  have hreg := reg_tprod_eq_G2C 1 (le_refl 1) 2 (by norm_num)
  unfold G2at1
  rw [← hreg, G2C_at_two_ofReal, dConst_prod_ofReal]
  unfold dConst
  rw [dConst_prod_eq_subtype]
  push_cast
  rw [show (((1:ℝ)/2 : ℝ) : ℂ) ^ (2:ℂ) = ((1:ℂ)/4) by
    rw [show ((2:ℂ)) = ((2:ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast
    ring]
  ring
