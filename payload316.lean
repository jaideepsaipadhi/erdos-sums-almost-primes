/-- Per-term bound for (10): each triple-sum term is at most
beta_i * 2^(-j) * 2^(-l-1) after using |g_i(s) - c_i| <= beta_i (s-1),
2^(-js) <= 2^(-j) on [1,2], and integral_log_pow_sub_one. -/
theorem Dk_term_bound (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    |∫ s in Set.Ioc (1:ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))|
      ≤ beta * (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ (l + 1)) := by
  have hdomint : MeasureTheory.IntegrableOn
      (fun s : ℝ => beta * (2:ℝ) ^ (-(j:ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)))
      (Set.Ioc (1:ℝ) 2) := by
    sorry
  have hptwise : ∀ s ∈ Set.Ioc (1:ℝ) 2,
      |((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))|
      ≤ beta * (2:ℝ) ^ (-(j:ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
    sorry
  sorry
