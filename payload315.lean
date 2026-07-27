/-- The frozen side as a triangular double sum of integrals.
Simpler than the Ik side: cCoeff is constant in s, and integrability is
integrable_Sm_integrand. -/
theorem Ikfrozen_re_eq_double_sum (k : ℕ) :
    (Ikfrozen k).re
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (∫ s in Set.Ioc (1:ℝ) 2,
          (cCoeff i).re * (2:ℝ) ^ (-(j:ℝ) * s)
            * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
  rw [Ikfrozen_re_eq]
  apply Finset.sum_congr rfl
  intro i _
  unfold Sm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro s _
  ring
