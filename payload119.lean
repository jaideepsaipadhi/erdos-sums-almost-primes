/-- Partial products of a HasProd family with all factors >= 1 are bounded
by the limit.  Real-specific version (Mathlib's prod_le_hasProd needs
IsOrderedMonoid, which R under multiplication is not). -/
theorem prod_le_tprod_real {f : ℕ → ℝ} {a : ℝ}
    (hone : ∀ i, (1:ℝ) ≤ f i) (hf : HasProd f a) (s : Finset ℕ) :
    ∏ i ∈ s, f i ≤ a := by
  refine ge_of_tendsto hf ?_
  refine Filter.eventually_atTop.2 ⟨s, fun t hst => ?_⟩
  apply Finset.prod_le_prod_of_subset_of_one_le' hst
  intro i _ _
  exact hone i
