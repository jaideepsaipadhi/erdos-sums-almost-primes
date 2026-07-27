/-- The p = 2 half of Lemma 3.9's c: d/ds log(1 - 2^(-s)) = log 2 / (2^s - 1). -/
theorem deriv_log_one_sub_two_pow (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t : ℝ => Real.log (1 - (2:ℝ) ^ (-t)))
      (Real.log 2 / ((2:ℝ) ^ s - 1)) s := by
  have h2s : (0:ℝ) < (2:ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hlt : (2:ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h1 : (2:ℝ) ^ (1:ℝ) < (2:ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h1
    linarith
  have hpos : (0:ℝ) < 1 - (2:ℝ) ^ (-s) := by linarith
  have hinner : HasDerivAt (fun t : ℝ => 1 - (2:ℝ) ^ (-t))
      ((2:ℝ) ^ (-s) * Real.log 2) s := by
    have hbase : HasDerivAt (fun t : ℝ => (2:ℝ) ^ (-t))
        (-((2:ℝ) ^ (-s) * Real.log 2)) s := by
      have h := (Real.hasDerivAt_const_rpow (by norm_num : (0:ℝ) < 2) s).comp s
        (hasDerivAt_neg s)
      simpa using h
    simpa using hbase.const_sub 1
  have h := (Real.hasDerivAt_log (ne_of_gt hpos)).comp s hinner
  convert h using 1
  field_simp
  rw [Real.rpow_neg (by norm_num)]
  field_simp
  ring
