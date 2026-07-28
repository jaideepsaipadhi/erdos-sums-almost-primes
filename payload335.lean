/-- d/ds [log 2 / (2^s - 1)] = -log^2(2) 2^s / (2^s - 1)^2.
The second derivative of the p = 2 part of Lemma 3.9's c.
Verified numerically at s = 1.3, 1.7, 2.0. -/
theorem deriv_two_pow_term (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t : ℝ => Real.log 2 / ((2:ℝ) ^ t - 1))
      (-((Real.log 2) ^ 2 * (2:ℝ) ^ s) / ((2:ℝ) ^ s - 1) ^ 2) s := by
  have h2s : (2:ℝ) ≤ (2:ℝ) ^ s := by
    calc (2:ℝ) = (2:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (2:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hs)
  have hne : (2:ℝ) ^ s - 1 ≠ 0 := by intro hcon; linarith
  have hbase : HasDerivAt (fun t : ℝ => (2:ℝ) ^ t) ((2:ℝ) ^ s * Real.log 2) s := by
    have hrw : (fun t : ℝ => (2:ℝ) ^ t)
        = fun t : ℝ => Real.exp (t * Real.log 2) := by
      funext t
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
    rw [hrw]
    have hinner : HasDerivAt (fun t : ℝ => t * Real.log 2) (Real.log 2) s := by
      simpa using (hasDerivAt_id s).mul_const (Real.log 2)
    have h := hinner.exp
    convert h using 1
    rw [show Real.exp (s * Real.log 2) = (2:ℝ) ^ s by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]]
  have hden : HasDerivAt (fun t : ℝ => (2:ℝ) ^ t - 1) ((2:ℝ) ^ s * Real.log 2) s := by
    simpa using hbase.sub_const 1
  have hstep := (hasDerivAt_const s (Real.log 2)).div hden hne
  have hval : -((Real.log 2) ^ 2 * (2:ℝ) ^ s) / ((2:ℝ) ^ s - 1) ^ 2
      = (0 * ((2:ℝ) ^ s - 1) - Real.log 2 * ((2:ℝ) ^ s * Real.log 2))
        / ((2:ℝ) ^ s - 1) ^ 2 := by
    field_simp
    ring
  rw [hval]
  exact hstep
