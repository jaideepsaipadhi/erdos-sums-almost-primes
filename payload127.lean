/-- Product monotonicity for nonnegative reals over a finset. -/
theorem finset_prod_le_prod_nonneg {s : Finset ℕ} {f g : ℕ → ℝ}
    (h0 : ∀ i ∈ s, (0:ℝ) ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : (0:ℝ) ≤ f a := h0 a (Finset.mem_insert_self a t)
    have hfa : f a ≤ g a := h1 a (Finset.mem_insert_self a t)
    have hrest : ∏ i ∈ t, f i ≤ ∏ i ∈ t, g i := by
      apply ih
      · intro i hi
        exact h0 i (Finset.mem_insert_of_mem hi)
      · intro i hi
        exact h1 i (Finset.mem_insert_of_mem hi)
    have hprodnn : (0:ℝ) ≤ ∏ i ∈ t, f i := by
      apply Finset.prod_nonneg
      intro i hi
      exact h0 i (Finset.mem_insert_of_mem hi)
    calc f a * ∏ i ∈ t, f i ≤ g a * ∏ i ∈ t, f i :=
          mul_le_mul_of_nonneg_right hfa hprodnn
      _ ≤ g a * ∏ i ∈ t, g i := by
          apply mul_le_mul_of_nonneg_left hrest
          linarith
