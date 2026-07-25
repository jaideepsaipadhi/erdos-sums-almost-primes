  have hsm : Summable (fun m : N.smoothNumbers => Norm.norm (zOmegaHom s z m)) := hgeo.1
  have hsum_le : (∑ x ∈ u, Norm.norm (zOmegaHom s z x))
      ≤ ∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m) := by
    rw [tsum_subtype]
    have hsm' : Summable (Set.indicator (N.smoothNumbers)
        (fun n : ℕ => Norm.norm (zOmegaHom s z n))) := by
      rwa [←  summable_subtype_iff_indicator]
    have hle : ∀ x ∈ u, Norm.norm (zOmegaHom s z x)
        ≤ Set.indicator (N.smoothNumbers)
          (fun n : ℕ => Norm.norm (zOmegaHom s z n)) x := by
      intro x hxu
      by_cases hx0 : x = 0
      · subst hx0
        rw [show zOmegaHom s z 0 = 0 from map_zero _]
        simp
      · rw [Set.indicator_of_mem (hsmooth x hxu hx0)]
    calc ∑ x ∈ u, Norm.norm (zOmegaHom s z x)
        ≤ ∑ x ∈ u, Set.indicator (N.smoothNumbers)
            (fun n : ℕ => Norm.norm (zOmegaHom s z n)) x := Finset.sum_le_sum hle
      _ ≤ ∑' x : ℕ, Set.indicator (N.smoothNumbers)
            (fun n : ℕ => Norm.norm (zOmegaHom s z n)) x := by
          apply hsm'.sum_le_tsum
          intro i _
          apply Set.indicator_nonneg
          intro a _
          exact norm_nonneg _
