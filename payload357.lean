/-- cBracket is s-continuous on {s // 1 <= s}: the kappa part (with fs held
fixed), the p = 3 term, and the tail series. -/
theorem cBracket_continuous_s (fs : ℝ) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} => cBracket fs (s:ℝ) z) := by
  have hsub : Continuous (fun s : {s : ℝ // 1 ≤ s} => (s:ℝ)) := continuous_subtype_val
  have hrpow2 : Continuous (fun s : {s : ℝ // 1 ≤ s} => (2:ℝ) ^ (s:ℝ)) :=
    (continuous_const_rpow (by norm_num)).comp hsub
  have h2ge : ∀ s : {s : ℝ // 1 ≤ s}, (2:ℝ) ≤ (2:ℝ) ^ (s:ℝ) := by
    intro s
    calc (2:ℝ) = (2:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (2:ℝ) ^ (s:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) s.2
  have hne : ∀ s : {s : ℝ // 1 ≤ s}, (2:ℝ) ^ (s:ℝ) - 1 ≠ 0 := by
    intro s hcon
    linarith [h2ge s]
  have hkap : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      z * (((fs + Real.log 2 / ((2:ℝ) ^ (s:ℝ) - 1) : ℝ)) : ℂ)) := by
    apply continuous_const.mul
    apply Complex.continuous_ofReal.comp
    exact continuous_const.add (continuous_const.div (hrpow2.sub continuous_const) hne)
  unfold cBracket
  apply hkap.add
  apply Continuous.add
  · exact cBracket_term_continuous_s 3 (le_refl 3) z hz
  · exact cBracket_series_continuous_s z hz
