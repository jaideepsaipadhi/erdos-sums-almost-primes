/-- Per-term s-continuity for cBracket's series on {s // 1 <= s}.
The denominators are nonvanishing there: p^s - 1 >= 2 and |p^s - z| >= 1
since p^s >= 3 and ||z|| <= 2. -/
theorem cBracket_term_continuous_s (p : ℕ) (hp : 3 ≤ p) (z : ℂ)
    (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      -(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ) - 1)
          / (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ) - z)) := by
  have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
  have hsub : Continuous (fun s : {s : ℝ // 1 ≤ s} => (s:ℝ)) := continuous_subtype_val
  have hrpow : Continuous (fun s : {s : ℝ // 1 ≤ s} => (((p:ℕ):ℝ)) ^ (s:ℝ)) :=
    (continuous_const_rpow (ne_of_gt hp0)).comp hsub
  have hps : ∀ s : {s : ℝ // 1 ≤ s}, (3:ℝ) ≤ (((p:ℕ):ℝ)) ^ (s:ℝ) := by
    intro s
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ (s:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) s.2
      _ ≤ (((p:ℕ):ℝ)) ^ (s:ℝ) := Real.rpow_le_rpow (by norm_num) hp3 (by linarith [s.2])
  have hcast : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ))) := Complex.continuous_ofReal.comp hrpow
  have hd1 : ∀ s : {s : ℝ // 1 ≤ s},
      (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ)) - 1 ≠ 0 := by
    intro s hcon
    rw [sub_eq_zero] at hcon
    have : ((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ) = 1 := by exact_mod_cast hcon
    linarith [hps s]
  have hd2 : ∀ s : {s : ℝ // 1 ≤ s},
      (((((((p:ℕ):ℝ)) ^ (s:ℝ) : ℝ)) : ℂ)) - z ≠ 0 := by
    intro s hcon
    rw [sub_eq_zero] at hcon
    rw [← hcon, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hps s] : (0:ℝ) < (((p:ℕ):ℝ)) ^ (s:ℝ))] at hz
    linarith [hps s]
  exact ((continuous_const.div (hcast.sub continuous_const) hd1).div
    (hcast.sub continuous_const) hd2)
