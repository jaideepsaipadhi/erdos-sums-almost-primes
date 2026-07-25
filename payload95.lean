theorem zOmega_prime_summable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) {p : ℕ} (hp : p.Prime) :
    Summable (fun n : ℕ => Norm.norm (zOmegaHom s z (p ^ n))) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    exact_mod_cast hp.pos
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by
    exact_mod_cast hp.two_le
  have hratio : Norm.norm z * ((p:ℝ) ^ (-s)) < 1 := by
    have h2s : (0:ℝ) < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hps : (p:ℝ) ^ (-s) ≤ (2:ℝ) ^ (-s) := by
      apply Real.rpow_le_rpow_of_exponent_nonpos
      · linarith
      · exact hp2
      · linarith
    have hinv : (2:ℝ) ^ (-s) = ((2:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    have hznn : (0:ℝ) ≤ Norm.norm z := norm_nonneg z
    calc Norm.norm z * ((p:ℝ) ^ (-s)) ≤ Norm.norm z * ((2:ℝ) ^ (-s)) := by
          apply mul_le_mul_of_nonneg_left hps hznn
      _ = Norm.norm z * ((2:ℝ) ^ s)⁻¹ := by rw [hinv]
      _ < 1 := by
          rw [mul_inv_lt_one_iff_of_pos h2s]
          exact hz
  sorry
