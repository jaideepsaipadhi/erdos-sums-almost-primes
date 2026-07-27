/-- The Ik-side integrand is integrable on (1,2], by domination against
integrable_Sm_integrand scaled by the gManu bound.  This is what unblocks the
sum-integral interchange in Dk_eq_triple_sum. -/
theorem integrable_Ik_term (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (gManu i s).re * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (Set.Ioc (1:ℝ) 2) := by
  have hdomIoc := (integrable_Sm_integrand l j).const_mul (Norm.norm (cCoeff i) + beta)
  have hdomIoo : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Norm.norm (cCoeff i) + beta) *
        ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (2:ℝ) ^ (-(j:ℝ) * s)))
      (Set.Ioo (1:ℝ) 2) :=
    hdomIoc.mono_set Set.Ioo_subset_Ioc_self
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (gManu i s).re * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) 2)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact Complex.continuous_re.comp_continuousOn (gManu_continuousOn i hderiv)
      · apply Continuous.continuousOn
        exact (continuous_const_rpow (by norm_num)).comp (continuous_const.mul continuous_id)
    · apply ContinuousOn.div_const
      apply ContinuousOn.pow
      apply ContinuousOn.neg
      apply Real.continuousOn_log.comp (continuousOn_id.sub continuousOn_const)
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, id_eq]
      intro hcon
      have : x = 1 := by linarith [sub_eq_zero.mp hcon]
      exact absurd this (ne_of_gt hx.1)
  have hIoo : MeasureTheory.IntegrableOn
      (fun s : ℝ => (gManu i s).re * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (Set.Ioo (1:ℝ) 2) := by
    apply MeasureTheory.Integrable.mono hdomIoo hmeas
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
    have hb := gManu_bounded i beta hbeta0 hderiv hbound M0 hM00 hM0 s hs
    have hre : |(gManu i s).re| ≤ Norm.norm (gManu i s) := Complex.abs_re_le_norm _
    have hlog : (0:ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
      apply div_nonneg _ (by positivity)
      apply pow_nonneg
      have : s - 1 ≤ 1 := by linarith [hs.2]
      have hpos : (0:ℝ) < s - 1 := by linarith [hs.1]
      simp only [neg_nonneg]
      exact Real.log_nonpos (le_of_lt hpos) this
    have h2 : (0:ℝ) < (2:ℝ) ^ (-(j:ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos h2, abs_of_nonneg hlog, abs_mul, abs_of_nonneg hlog, abs_of_pos h2]
    have hcb : (0:ℝ) ≤ Norm.norm (cCoeff i) + beta := by positivity
    nlinarith [hre, hb, hlog, h2, abs_nonneg ((gManu i s).re)]
  exact hIoo.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc
