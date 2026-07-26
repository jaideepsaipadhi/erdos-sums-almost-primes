theorem correction_le_one_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    20 * (p:ℝ) ^ (-2*s) ≤ 1 := by
  have hp5 : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hpos : (0:ℝ) < (p:ℝ) := by linarith
  have h1 : (p:ℝ) ^ (-2*s) ≤ (p:ℝ) ^ (-2:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpow : (5:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2:ℝ) :=
    Real.rpow_le_rpow (by norm_num) hp5 (by norm_num)
  have heq5 : (5:ℝ) ^ (-2:ℝ) = ((5:ℝ) ^ (2:ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) 2
  have heqp : (p:ℝ) ^ (-2:ℝ) = ((p:ℝ) ^ (2:ℝ))⁻¹ :=
    Real.rpow_neg hpos.le 2
  have h2 : (p:ℝ) ^ (-2:ℝ) ≤ (5:ℝ) ^ (-2:ℝ) := by
    rw [heqp, heq5]
    gcongr
  have h5val : (5:ℝ) ^ (-2:ℝ) = 1/25 := by
    rw [heq5]
    norm_num [Real.rpow_natCast]
  have hchain : (p:ℝ) ^ (-2*s) ≤ 1/25 := le_trans h1 (h2.trans_eq h5val)
  linarith [hchain]

