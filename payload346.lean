/-- MANUSCRIPT Theorem 6.1: S_2(m) = sum_{j+l=m} int_1^2 (-log(s-1))^l/l!
(s-1) 2^(-js) ds.  The (s-1)-weighted analogue of Sm. -/
noncomputable def S2m (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ∫ s in Set.Ioc (1:ℝ) 2,
      (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (s - 1)
        * (2:ℝ) ^ (-(j:ℝ) * s)

/-- MANUSCRIPT Theorem 6.1: A^(2)_m = 2^m S_2(m). -/
noncomputable def A2m (m : ℕ) : ℝ := (2:ℝ) ^ m * S2m m

/-- S_2's integrand is integrable on (1,2], dominated by the (s-1)-weighted
integrand of integrable_log_pow_sub_one since 2^(-js) <= 1 there. -/
theorem integrable_S2_integrand (l j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
        * (2:ℝ) ^ (-(j:ℝ) * s))
      (Set.Ioc (1:ℝ) 2) := by
  have hdom := integrable_log_pow_sub_one l
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
        * (2:ℝ) ^ (-(j:ℝ) * s))
      (MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) 2)) := by
    apply MeasureTheory.AEStronglyMeasurable.mul _ _
    · exact hdom.aestronglyMeasurable
    · apply Continuous.aestronglyMeasurable
      exact (continuous_const_rpow (by norm_num)).comp
        (continuous_const.mul continuous_id)
  apply MeasureTheory.Integrable.mono hdom hmeas
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
  have hs1 : (1:ℝ) < s := hs.1
  have hs2 : s ≤ 2 := hs.2
  have hLpos : (0:ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) := by
    apply mul_nonneg _ (by linarith)
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  have h2 : (2:ℝ) ^ (-(j:ℝ) * s) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0:ℝ) ≤ (j:ℝ) := by positivity
    nlinarith [hs1]
  have h2pos : (0:ℝ) < (2:ℝ) ^ (-(j:ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hLpos,
    abs_of_pos h2pos, abs_of_nonneg hLpos]
  nlinarith [hLpos, h2, h2pos]
