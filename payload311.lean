/-- The Ik-side integrand is integrable on (1,2], by domination against
integrable_Sm_integrand scaled by the gManu bound.  This is what unblocks the
sum-integral interchange in Dk_eq_triple_sum. -/
theorem integrable_Ik_term (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (gManu i s).re * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (Set.Ioc (1:ℝ) 2) := by
  sorry
