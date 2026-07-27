/-- The complex argument 1 - c*p^(-s) lies in the slit plane, for ||c|| <= 2,
p >= 3, s >= 1: its distance from 1 is at most 2/3, so its real part exceeds
1/3.  This is the side condition Complex.hasDerivAt_log needs. -/
theorem one_sub_mem_slitPlane (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (c : ℂ) (hc : Norm.norm c ≤ 2) :
    (1 : ℂ) - c * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ) ∈ Complex.slitPlane := by
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by linarith
  have hppos : (0:ℝ) < ((p:ℕ):ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hthird : ((p:ℕ):ℝ) ^ (-s) ≤ 1/3 := by
    have h1 : ((p:ℕ):ℝ) ^ (-s) ≤ ((p:ℕ):ℝ) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : (((p:ℕ):ℝ))⁻¹ ≤ 1/3 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hnorm : Norm.norm (c * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ≤ 2/3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos]
    nlinarith [norm_nonneg c, hc, hthird, hppos]
  rw [Complex.mem_slitPlane_iff]
  left
  have hre : (((1 : ℂ) - c * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))).re
      = 1 - (c * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)).re := by
    simp
  rw [hre]
  have habs : |(c * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)).re|
      ≤ Norm.norm (c * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) := Complex.abs_re_le_norm _
  have := abs_le.mp (le_trans habs hnorm)
  linarith [this.2]
