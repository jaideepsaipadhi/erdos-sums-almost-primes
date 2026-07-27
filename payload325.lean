/-- The r=2 per-prime derivative:
d/ds [-(z-1) log p / ((p^s-1)(p^s-z))]
  = (z-1) log^2 p * p^s * ((p^s-z) + (p^s-1)) / ((p^s-1)^2 (p^s-z)^2).
Verified numerically at (p,s,z) = (3,1.4,1.3), (5,1.7,0.9), (11,1.2,1.8). -/
theorem deriv2_prime_term (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -((z - 1) * Real.log (p:ℝ)) / (((p:ℝ)) ^ t - 1) / (((p:ℝ)) ^ t - z))
      ((z - 1) * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ s)
        * (((((p:ℝ)) ^ s - z) + (((p:ℝ)) ^ s - 1)))
        / ((((p:ℝ)) ^ s - 1) ^ 2 * ((((p:ℝ)) ^ s - z)) ^ 2)) s := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (3:ℝ) ≤ ((p:ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p:ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hzabs := abs_le.mp hz
  have hd1 : ((p:ℝ)) ^ s - 1 ≠ 0 := by intro hcon; linarith
  have hd2 : ((p:ℝ)) ^ s - z ≠ 0 := by
    intro hcon
    have := hzabs.2
    linarith
  have hbase := hasDerivAt_rpow_pos p hp s
  have hA : HasDerivAt (fun t : ℝ => ((p:ℝ)) ^ t - 1)
      (((p:ℝ)) ^ s * Real.log (p:ℝ)) s := by
    simpa using hbase.sub_const 1
  have hB : HasDerivAt (fun t : ℝ => ((p:ℝ)) ^ t - z)
      (((p:ℝ)) ^ s * Real.log (p:ℝ)) s := by
    simpa using hbase.sub_const z
  have hstep1 := (hasDerivAt_const s (-((z - 1) * Real.log (p:ℝ)))).div hA hd1
  have hstep2 := hstep1.div hB hd2
  convert hstep2 using 1
  field_simp
  ring
