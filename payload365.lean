/-- Second-order Taylor bound: if phi is differentiable on (1,2) with
||phi'(x)|| <= g (x-1) there, and phi(t) -> 0 as t -> 1+, then
||phi(s)|| <= g (s-1)^2 / 2.

This is the step that turns the first-order bound of deriv_sub_limit_bound
into the quadratic remainder of Theorem 6.1.  Proved by the same
interior-plus-limit route, with the interior step bounding
||phi(s) - phi(t)|| by the integral of the linear bound. -/
theorem quadratic_remainder_bound (phi : ℝ → ℂ) (g : ℝ) (hg0 : 0 ≤ g)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2, HasDerivAt phi (deriv phi x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2, Norm.norm (deriv phi x) ≤ g * (x - 1))
    (hlim : Filter.Tendsto phi (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds 0))
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    Norm.norm (phi s) ≤ g * (s - 1) ^ 2 / 2 := by
  have hlin : ∀ t : ℝ, t ∈ Set.Ioo (1:ℝ) s →
      ‖phi s - phi t‖ ≤ g * ((s - 1) ^ 2 - (t - 1) ^ 2) / 2 := by
    intro t ht
    have hts : t ≤ s := le_of_lt ht.2
    have hsub : Set.uIcc t s ⊆ Set.Ioo (1:ℝ) 2 := by
      rw [Set.uIcc_of_le hts]
      intro x hx
      exact Set.mem_Ioo.mpr ⟨lt_of_lt_of_le ht.1 hx.1, lt_of_le_of_lt hx.2 hs.2⟩
    have hint : IntervalIntegrable (fun x : ℝ => deriv phi x) MeasureTheory.volume t s := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hts]
      intro x hx
      exact ((hderiv x (hsub (by rw [Set.uIcc_of_le hts]; exact hx))).continuousAt).continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (hsub hx)) hint
    rw [← hftc]
    have hbnd : ‖∫ y in t..s, deriv phi y‖ ≤ ∫ y in t..s, g * (y - 1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hts
      · filter_upwards with y hy
        exact hbound y (hsub (by rw [Set.uIcc_of_le hts]; exact ⟨le_of_lt hy.1, hy.2⟩))
      · apply ContinuousOn.intervalIntegrable
        exact (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    have heval : (∫ y in t..s, g * (y - 1)) = g * ((s - 1) ^ 2 - (t - 1) ^ 2) / 2 := by
      have hd : ∀ y ∈ Set.uIcc t s,
          HasDerivAt (fun x : ℝ => g * (x - 1) ^ 2 / 2) (g * (y - 1)) y := by
        intro y _
        have h1 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1)) y := by
          have := ((hasDerivAt_id y).sub_const 1).pow 2
          simpa using this
        have h2 := (h1.const_mul g).div_const 2
        convert h2 using 1
        ring
      rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable t s)]
    rw [heval] at hbnd
    exact hbnd
  have hsublim : Filter.Tendsto (fun t : ℝ => ‖phi s - phi t‖)
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds ‖phi s - 0‖) := by
    apply Filter.Tendsto.norm
    exact tendsto_const_nhds.sub hlim
  simp only [sub_zero] at hsublim
  apply le_of_tendsto hsublim
  filter_upwards [Ioo_mem_nhdsGT hs.1] with t ht
  have h := hlin t ht
  have hsq : (0:ℝ) ≤ (t - 1) ^ 2 := sq_nonneg _
  nlinarith [h, hsq, hg0]
