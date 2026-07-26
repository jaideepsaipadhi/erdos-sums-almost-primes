/-- Expanding (k-i)^2 under the sum: the quadratic weight splits into the
three partial sums of section 2.3. -/
theorem sum_two_pow_sq_expand (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        (2:ℝ)^i * (cCoeff i).re * ((k:ℝ) - (i:ℝ))^2
      = (k:ℝ)^2 * (dConst - Wk k) - 2 * (k:ℝ) * Uk k + Vk k := by
  have hexp : ∀ i ∈ Finset.range (k + 1),
      (2:ℝ)^i * (cCoeff i).re * ((k:ℝ) - (i:ℝ))^2
        = (k:ℝ)^2 * ((2:ℝ)^i * (cCoeff i).re)
          - 2 * (k:ℝ) * ((i:ℝ) * (2:ℝ)^i * (cCoeff i).re)
          + ((i:ℝ)^2 * (2:ℝ)^i * (cCoeff i).re) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [cCoeff_two_pow_partial_sum]
  unfold Uk Vk
  ring
