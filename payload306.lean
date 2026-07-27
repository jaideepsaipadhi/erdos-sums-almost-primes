/-- MANUSCRIPT section 3.5, the mean value step:
||g_i(s) - c_i|| <= (s-1) * beta_i for s in (1,2).
The endpoint is reached by a limit rather than by evaluation: gManu i 1 is a
junk value (kappaFac 1 = 0), so c_i enters through gManu_tendsto_cCoeff. -/
theorem gManu_sub_cCoeff_bound (i : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0)
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    Norm.norm (gManu i s - cCoeff i) ≤ beta * (s - 1) := by
  have hlim := gManu_tendsto_cCoeff i M0 hM00 hM0
  have hsublim : Filter.Tendsto (fun t : ℝ => Norm.norm (gManu i s - gManu i t))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (Norm.norm (gManu i s - cCoeff i))) := by
    apply Filter.Tendsto.norm
    exact tendsto_const_nhds.sub hlim
  have hmem : Set.Ioo (1:ℝ) s ∈ nhdsWithin (1:ℝ) (Set.Ioi (1:ℝ)) :=
    Ioo_mem_nhdsWithin_Ioi (Set.mem_Ico.mpr (⟨ le_refl 1, hs.1 ⟩))
  have hbnd : ∀ᶠ t in nhdsWithin 1 (Set.Ioi (1:ℝ)),
      Norm.norm (gManu i s - gManu i t) ≤ beta * (s - 1) := by
    filter_upwards [hmem] with t ht
    have ht2 : t ∈ Set.Ioo (1:ℝ) 2 :=
      Set.mem_Ioo.mpr (⟨ ht.1, lt_trans ht.2 hs.2 ⟩)
    have hlip := gManu_lipschitz_interior i beta hderiv hbound t s ht2 hs
    have hst : Norm.norm (s - t) ≤ s - 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
      linarith [ht.1]
    calc Norm.norm (gManu i s - gManu i t) ≤ beta * Norm.norm (s - t) := hlip
      _ ≤ beta * (s - 1) := by
          apply mul_le_mul_of_nonneg_left hst hbeta0
  exact le_of_tendsto hsublim hbnd
