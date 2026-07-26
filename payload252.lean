/-- The real part of the frozen integral distributes over the sum, and each
term's real part is (c_i).re * S(k-i) since S is real. -/
theorem Ikfrozen_re_eq (k : ℕ) :
    (Ikfrozen k).re = ∑ i ∈ Finset.range (k + 1), (cCoeff i).re * Sm (k - i) := by
  unfold Ikfrozen
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring
