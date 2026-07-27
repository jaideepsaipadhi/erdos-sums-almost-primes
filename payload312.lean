/-- Real-valued conv_flatten: the triangular double sum as a sigma sum. -/
theorem conv_flatten_real (k : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k - p + 1), g p q
      = ∑ x ∈ (Finset.range (k + 1)).sigma (fun p => Finset.range (k - p + 1)),
          g x.1 x.2 := by
  rw [Finset.sum_sigma]

/-- Swapping the two indices of a triangular double sum.
Fk_expansion_manu sums (2-index outer, g-index inner); Ikfrozen sums the other
way round.  This reconciles them. -/
theorem triangular_sum_comm (k : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k - p + 1), g p q
      = ∑ q ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (k - q + 1), g p q := by
  rw [conv_flatten_real, conv_flatten_real]
  apply Finset.sum_nbij'
    (i := fun x : Sigma (fun _ : ℕ => ℕ) => Sigma.mk x.2 x.1)
    (j := fun y : Sigma (fun _ : ℕ => ℕ) => Sigma.mk y.2 y.1)
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · intro x _
    rfl
  · intro y _
    rfl
  · intro x _
    rfl
