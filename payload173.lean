/-- Polynomial growth is dominated by geometric growth, with a uniform constant. -/
theorem pow_le_const_mul_geom (j : ℕ) {c : ℝ} (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ((m:ℕ):ℝ) ^ j ≤ C * c ^ m := by
  have hlo := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) j hc
  obtain ⟨ C0, hC0 ⟩ := hlo.isBigO.bound
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp hC0
  refine ⟨ max (max C0 1) (((N:ℕ):ℝ) ^ j + 1), ?_, ?_⟩
  · have h1 : (0:ℝ) < 1 := one_pos
    have : (1:ℝ) ≤ max C0 1 := le_max_right _ _
    calc (0:ℝ) < 1 := h1
      _ ≤ max C0 1 := this
      _ ≤ max (max C0 1) (((N:ℕ):ℝ) ^ j + 1) := le_max_left _ _
  · intro m
    have hcm : (0:ℝ) < c ^ m := by positivity
    have hcm1 : (1:ℝ) ≤ c ^ m := one_le_pow_of_le_of_nonneg (le_of_lt hc) m
    rcases Nat.lt_or_ge m N with hlt | hge
    · have hmN : ((m:ℕ):ℝ) ^ j ≤ ((N:ℕ):ℝ) ^ j := by
        apply pow_le_pow_left (by positivity)
        exact_mod_cast le_of_lt hlt
      calc ((m:ℕ):ℝ) ^ j ≤ ((N:ℕ):ℝ) ^ j := hmN
        _ ≤ (((N:ℕ):ℝ) ^ j + 1) * 1 := by linarith
        _ ≤ (((N:ℕ):ℝ) ^ j + 1) * c ^ m := by
            apply mul_le_mul_of_nonneg_left hcm1 (by positivity)
        _ ≤ max (max C0 1) (((N:ℕ):ℝ) ^ j + 1) * c ^ m := by
            apply mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hcm)
    · have hb := hN m hge
      simp only [Real.norm_eq_abs] at hb
      have habs : ((m:ℕ):ℝ) ^ j ≤ C0 * c ^ m := by
        calc ((m:ℕ):ℝ) ^ j ≤ |((m:ℕ):ℝ) ^ j| := le_abs_self _
          _ ≤ C0 * |c ^ m| := hb
          _ = C0 * c ^ m := by rw [abs_of_pos hcm]
      calc ((m:ℕ):ℝ) ^ j ≤ C0 * c ^ m := habs
        _ ≤ max (max C0 1) (((N:ℕ):ℝ) ^ j + 1) * c ^ m := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hcm)
            exact le_trans (le_max_left C0 1) (le_max_left _ _)
