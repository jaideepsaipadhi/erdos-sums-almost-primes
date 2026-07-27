/-- G2tailC is continuous in s on {s // 1 <= s}: it is exp of the correction
series (G2tailC_eq_exp_sum), which is continuous by
correction_series_continuous_s. -/
theorem G2tailC_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} => G2tailC (s:ℝ) z) := by
  have hser := correction_series_continuous_s z hz
  have hexp := Complex.continuous_exp.comp hser
  apply hexp.congr
  intro s
  exact (G2tailC_eq_exp_sum (s:ℝ) s.2 z hz).symm
