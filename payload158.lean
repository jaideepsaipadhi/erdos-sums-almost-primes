  have hcpow := cpow_neg_tprod_eq_cFac s hs z hz hc hmulR hposR hlogR
  have hreg := (reg_multipliable_three s (le_of_lt hs) z hz).hasProd
  have hmul := hcpow.mul hreg
  rw [reg_tprod_eq_G2C s (le_of_lt hs) z hz] at hmul
  apply hmul.congr_fun
  intro p
  have hpos : (0:ℝ) < 1 - ((p:ℕ):ℝ) ^ (-s) := hposR p |> inv_pos.mp
  exact euler_factor_split (((p:ℕ):ℝ) ^ (-s)) hpos z (z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))
