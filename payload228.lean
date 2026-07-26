theorem prime_factor_sub_one_bound_complex_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 5/2) :
    ‖Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖
      ≤ 40 * (p:ℝ) ^ (-2*s) := by
  set c : ℂ := (-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
    z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ) with hc_def
  have hp3 : 5 ≤ p := by omega
  have hbound : ‖c‖ ≤ 20 * (p:ℝ) ^ (-2*s) := prime_correction_bound_complex_wide p hp3 s hs z hz
  have hle1 : 20 * (p:ℝ) ^ (-2*s) ≤ 1 := correction_le_one_wide p hp s hs
  have hc1 : ‖c‖ ≤ 1 := le_trans hbound hle1
  calc ‖Complex.exp c - 1‖ ≤ 2 * ‖c‖ := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (20 * (p:ℝ) ^ (-2*s)) := by linarith [hbound]
    _ = 40 * (p:ℝ) ^ (-2*s) := by ring

