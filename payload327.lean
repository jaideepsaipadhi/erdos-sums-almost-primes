theorem deriv2_clog_prime_term (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ))
          / (((((p:ℝ)) ^ t : ℝ) : ℂ) - 1) / (((((p:ℝ)) ^ t : ℝ) : ℂ) - z))
      ((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ) ^ 2 * ((((p:ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p:ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p:ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p:ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))) s := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (3:ℝ) ≤ ((p:ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p:ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hpsC : Norm.norm ((((p:ℝ)) ^ s : ℝ) : ℂ) = ((p:ℝ)) ^ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hd1 : ((((p:ℝ)) ^ s : ℝ) : ℂ) - 1 ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    have : ((p:ℝ)) ^ s = 1 := by exact_mod_cast hcon
    linarith
  have hd2 : ((((p:ℝ)) ^ s : ℝ) : ℂ) - z ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    rw [← hcon, hpsC] at hz
    linarith
  have hbase : HasDerivAt (fun t : ℝ => ((((p:ℝ)) ^ t : ℝ) : ℂ))
      (((((p:ℝ)) ^ s * Real.log (p:ℝ) : ℝ)) : ℂ) s :=
    (hasDerivAt_rpow_pos p hp s).ofReal_comp
  have hA : HasDerivAt (fun t : ℝ => ((((p:ℝ)) ^ t : ℝ) : ℂ) - 1)
      (((((p:ℝ)) ^ s * Real.log (p:ℝ) : ℝ)) : ℂ) s := by
    simpa using hbase.sub_const 1
  have hB : HasDerivAt (fun t : ℝ => ((((p:ℝ)) ^ t : ℝ) : ℂ) - z)
      (((((p:ℝ)) ^ s * Real.log (p:ℝ) : ℝ)) : ℂ) s := by
    simpa using hbase.sub_const z
  have hstep1 := (hasDerivAt_const s (-((z - 1) * ((Real.log (p:ℝ) : ℝ) : ℂ)))).div hA hd1
  have hstep2 := hstep1.div hB hd2
  convert hstep2 using 1
  sorry
