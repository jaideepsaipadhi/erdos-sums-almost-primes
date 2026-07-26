/-- cFac s = exp of the convergent sum of logs, hence positive.
DISCHARGES the hc : 0 < cFac s hypothesis threaded through A3 and Lemma 2.2. -/
theorem cFac_eq_exp_log_sum (s : ℝ) (hs : 1 < s) :
    cFac s = Real.exp (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)) := by
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹ := by
    intro p
    obtain ⟨ h3, hp ⟩ := cFac_factor_le_third s hs p
    apply inv_pos.mpr
    linarith
  have hlog := cFac_log_summable s hs
  have hprod := hasProd_of_hasSum_log hpos hlog.hasSum
  unfold cFac
  exact hprod.tprod_eq

theorem cFac_pos (s : ℝ) (hs : 1 < s) : 0 < cFac s := by
  rw [cFac_eq_exp_log_sum s hs]
  exact Real.exp_pos _
