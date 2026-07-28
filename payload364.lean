/-- First-order Taylor step: if D is differentiable on (1,2) with ||D'|| <= g
there, and D(s) -> b as s -> 1+, then ||D(s) - b|| <= g (s-1).
Abstracted from gManu_sub_cCoeff_bound: the same interior-Lipschitz plus
endpoint-limit argument, stated for an arbitrary D so it serves both
D = g_i (giving the beta bound) and D = d_s g_i (giving the gammahat bound). -/
theorem deriv_sub_limit_bound (D : ℝ → ℂ) (b : ℂ) (g : ℝ) (hg0 : 0 ≤ g)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2, HasDerivAt D (deriv D x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2, Norm.norm (deriv D x) ≤ g)
    (hlim : Filter.Tendsto D (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds b))
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    Norm.norm (D s - b) ≤ g * (s - 1) := by
  have hsublim : Filter.Tendsto (fun t : ℝ => Norm.norm (D s - D t))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (Norm.norm (D s - b))) := by
    apply Filter.Tendsto.norm
    exact tendsto_const_nhds.sub hlim
  have hmem : Set.Ioo (1:ℝ) s ∈ nhdsWithin (1:ℝ) (Set.Ioi (1:ℝ)) :=
    Ioo_mem_nhdsGT hs.1
  have hbnd : ∀ᶠ t in nhdsWithin 1 (Set.Ioi (1:ℝ)),
      Norm.norm (D s - D t) ≤ g * (s - 1) := by
    filter_upwards [hmem] with t ht
    have ht2 : t ∈ Set.Ioo (1:ℝ) 2 :=
      Set.mem_Ioo.mpr (⟨ ht.1, lt_trans ht.2 hs.2 ⟩)
    have hlip : Norm.norm (D s - D t) ≤ g * Norm.norm (s - t) := by
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f' := fun x : ℝ => deriv D x)
        (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_Ioo 1 2) ht2 hs
    have hst : Norm.norm (s - t) ≤ s - 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
      linarith [ht.1]
    calc Norm.norm (D s - D t) ≤ g * Norm.norm (s - t) := hlip
      _ ≤ g * (s - 1) := mul_le_mul_of_nonneg_left hst hg0
  exact le_of_tendsto hsublim hbnd
