/-- Lemma 3.9's per-prime term, assembled from two applications of
deriv_log_one_sub_const_rpow (at c = z and c = 1).
The cancellation between the two logs is what produces p^(-2s) decay;
bounding them separately would give only p^(-s), which is not summable. -/
theorem deriv_log_prime_factor (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -Real.log (1 - z * ((p:ℝ)) ^ (-t)) + z * Real.log (1 - ((p:ℝ)) ^ (-t)))
      (-(z * (z - 1) * Real.log (p:ℝ))
        / ((((p:ℝ)) ^ s - 1) * (((p:ℝ)) ^ s - z))) s := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (3:ℝ) ≤ ((p:ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p:ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hneg : ((p:ℝ)) ^ (-s) = (((p:ℝ)) ^ s)⁻¹ := Real.rpow_neg (le_of_lt hp0) s
  have hpsinv : ((p:ℝ)) ^ (-s) ≤ 1/3 := by
    rw [hneg, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hppos : (0:ℝ) < ((p:ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hzabs := abs_le.mp hz
  have hne1 : (1:ℝ) - z * ((p:ℝ)) ^ (-s) ≠ 0 := by
    have : z * ((p:ℝ)) ^ (-s) ≤ 2/3 := by nlinarith [hzabs.2, hppos, hpsinv]
    intro hcon
    have : z * ((p:ℝ)) ^ (-s) = 1 := by linarith
    linarith
  have hne2 : (1:ℝ) - (1:ℝ) * ((p:ℝ)) ^ (-s) ≠ 0 := by
    rw [one_mul]
    intro hcon
    have : ((p:ℝ)) ^ (-s) = 1 := by linarith
    linarith
  have hA := (deriv_log_one_sub_const_rpow p hp z s hne1).neg
  have hB := (deriv_log_one_sub_const_rpow p hp 1 s hne2).const_mul z
  simp only [one_mul] at hB
  have hsum := hA.add hB
  have hval : -(z * (z - 1) * Real.log (p:ℝ))
        / ((((p:ℝ)) ^ s - 1) * (((p:ℝ)) ^ s - z))
      = -(z * Real.log (p:ℝ) * ((p:ℝ)) ^ (-s) / (1 - z * ((p:ℝ)) ^ (-s)))
        + z * (1 * Real.log (p:ℝ) * ((p:ℝ)) ^ (-s) / (1 - 1 * ((p:ℝ)) ^ (-s))) := by
    rw [one_mul, one_mul, hneg]
    have hps0 : ((p:ℝ)) ^ s ≠ 0 := by linarith
    have hd1 : (1:ℝ) - z * (((p:ℝ)) ^ s)⁻¹ ≠ 0 := by rw [← hneg]; exact hne1
    have hd2 : (1:ℝ) - (((p:ℝ)) ^ s)⁻¹ ≠ 0 := by
      rw [← hneg]; simpa using hne2
    field_simp
    ring
  rw [hval]
  exact hsum
