/-- For s > 1 there is a radius strictly between 3/2 and the summability threshold. -/
theorem exists_radius_gap (s : ℝ) (hs : 1 < s) :
    ∃ r : ℝ, 3/2 < r ∧ r * ((3:ℝ) ^ (-s)) ≤ 1/2 ∧ r < (2:ℝ) ^ s := by
  have h3s : (3:ℝ) < (3:ℝ) ^ s := by
    have h1 : (3:ℝ) ^ (1:ℝ) < (3:ℝ) ^ s := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rwa [Real.rpow_one] at h1
  have h2s : (2:ℝ) ≤ (2:ℝ) ^ s := by
    have h1 : (2:ℝ) ^ (1:ℝ) ≤ (2:ℝ) ^ s := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rwa [Real.rpow_one] at h1
  set M : ℝ := min ((3:ℝ) ^ s / 2) ((2:ℝ) ^ s) with hM
  have hMgt : 3/2 < M := by
    rw [hM, lt_min_iff]
    constructor
    · linarith
    · linarith
  refine ⟨ (3/2 + M) / 2, by linarith, ?_, ?_⟩
  · have hle : (3/2 + M) / 2 ≤ (3:ℝ) ^ s / 2 := by
      have : M ≤ (3:ℝ) ^ s / 2 := min_le_left _ _
      linarith
    have h3pos : (0:ℝ) < (3:ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
    have hinv : (3:ℝ) ^ (-s) = ((3:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    have h3spos : (0:ℝ) < (3:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    rw [hinv]
    rw [mul_inv_le_iff0 h3spos]
    linarith
  · have : M ≤ (2:ℝ) ^ s := min_le_right _ _
    linarith
