/-- D3: the complex p >= 3 product at z = 2 is the cast of the real one. -/
theorem G2C_at_two_ofReal :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - (2:ℂ) * ((((p:ℕ):ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ))⁻¹
          * (((1 - ((p:ℕ):ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ)) ^ (2:ℂ))
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (((((1 - 2 * ((p:ℕ):ℝ) ^ (-(1:ℝ)) : ℝ))⁻¹
            * ((1 - ((p:ℕ):ℝ) ^ (-(1:ℝ)) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
  apply tprod_congr
  intro p
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
  have hle : ((p:ℕ):ℝ) ^ (-(1:ℝ)) ≤ 1/3 := by
    rw [Real.rpow_neg_one]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hpos : (0:ℝ) < ((p:ℕ):ℝ) ^ (-(1:ℝ)) := by positivity
  have hne : (1:ℝ) - 2 * (((p:ℕ):ℝ) ^ (-(1:ℝ))) ≠ 0 := by
    have : 2 * (((p:ℕ):ℝ) ^ (-(1:ℝ))) ≤ 2/3 := by linarith
    intro hcon
    linarith
  exact reg_factor_at_two (((p:ℕ):ℝ) ^ (-(1:ℝ))) hne
