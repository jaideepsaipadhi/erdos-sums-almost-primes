/-- The per-prime norm bound, in the form the geometric machinery wants. -/
theorem zOmegaNorm_prime_lt_one (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) {p : ℕ} (hp : p.Prime) :
    Norm.norm (zOmegaNormHom s z p) < 1 := by
  have hval : zOmegaNormHom s z p = Norm.norm z * ((p:ℝ) ^ (-s)) := by
    have h := zOmegaNorm_prime_pow s z hp 1
    rw [pow_one, pow_one] at h
    exact h
  have hnn : (0:ℝ) ≤ Norm.norm z * ((p:ℝ) ^ (-s)) := by positivity
  rw [hval, Real.norm_eq_abs, abs_of_nonneg hnn]
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have h2s : (0:ℝ) < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hps : (p:ℝ) ^ (-s) ≤ (2:ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (p:ℝ)),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    gcongr
  have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
  have hinvpos : (0:ℝ) < ((2:ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
  calc Norm.norm z * ((p:ℝ) ^ (-s)) ≤ Norm.norm z * ((2:ℝ) ^ (-s)) :=
        mul_le_mul_of_nonneg_left hps hznn
    _ = Norm.norm z * ((2:ℝ) ^ s)⁻¹ := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    _ < 1 := by
        have hkey := mul_lt_mul_of_pos_right hz hinvpos
        rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
