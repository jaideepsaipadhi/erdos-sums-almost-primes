/-- gManu i is bounded on (1,2) by ||c_i|| + beta_i, from the mean value step.
This is what makes the Ik-side integrands dominated, hence integrable, hence
the sum-integral interchange of Dk_eq_triple_sum available. -/
theorem gManu_bounded (i : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0)
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    Norm.norm (gManu i s) ≤ Norm.norm (cCoeff i) + beta := by
  have hmv := gManu_sub_cCoeff_bound i beta hbeta0 hderiv hbound M0 hM00 hM0 s hs
  have hs1 : s - 1 ≤ 1 := by linarith [hs.2]
  have hbs : beta * (s - 1) ≤ beta := by
    calc beta * (s - 1) ≤ beta * 1 := by
          apply mul_le_mul_of_nonneg_left hs1 hbeta0
      _ = beta := mul_one beta
  calc Norm.norm (gManu i s)
      = Norm.norm ((gManu i s - cCoeff i) + cCoeff i) := by ring_nf
    _ ≤ Norm.norm (gManu i s - cCoeff i) + Norm.norm (cCoeff i) := norm_add_le _ _
    _ ≤ beta * (s - 1) + Norm.norm (cCoeff i) := by linarith [hmv]
    _ ≤ beta + Norm.norm (cCoeff i) := by linarith [hbs]
    _ = Norm.norm (cCoeff i) + beta := by ring
