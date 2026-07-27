/-- Per-term continuity in theta on the contour |z| = 2.
Both denominators are nonvanishing there: p^s - 1 >= 2 is constant in theta,
and |p^s - z| >= p^s - 2 >= 1 since |z| = 2 and p^s >= 3. -/
theorem clog_term_continuous_theta (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      -(circleMap 0 (2:ℝ) theta * (circleMap 0 (2:ℝ) theta - 1)
          * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2:ℝ) theta)) := by
  have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
  have hps : (3:ℝ) ≤ (((p:ℕ):ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p:ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hcm : Continuous (circleMap 0 (2:ℝ)) := continuous_circleMap 0 _
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2:ℝ) theta) = 2 := by
    intro theta
    simp [circleMap]
  have hd1 : (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1) ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    have : ((((p:ℕ):ℝ)) ^ s : ℝ) = 1 := by exact_mod_cast hcon
    linarith
  have hd2 : ∀ theta : ℝ,
      (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2:ℝ) theta) ≠ 0 := by
    intro theta hcon
    rw [sub_eq_zero] at hcon
    have hn := hnorm theta
    rw [← hcon, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < (((p:ℕ):ℝ)) ^ s)] at hn
    linarith
  apply Continuous.div _ continuous_const (fun theta => hd2 theta)
  apply Continuous.div _ continuous_const (fun _ => hd1)
  apply Continuous.neg
  apply Continuous.mul _ continuous_const
  exact hcm.mul (hcm.sub continuous_const)
