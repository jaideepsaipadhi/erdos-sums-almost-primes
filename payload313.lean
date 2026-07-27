/-- MANUSCRIPT (4): D_k as a triple sum.
D_k = sum_{i+j+l=k} int_1^2 (g_i(s) - c_i) 2^(-js) (-log(s-1))^l/l! ds.
Both Ik and Ikfrozen become triangular double sums over the same region; the
index orders differ (triangular_sum_comm reconciles them) and the finite sums
pass through the integral (integrable_Ik_term and integrable_Sm_integrand). -/
theorem Dk_eq_triple_sum (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    Dk k = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
      (∫ s in Set.Ioc (1:ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
  sorry
