/-- MANUSCRIPT (10): |E_1(k)| <= (1/2) sum_{i<=k} beta_i 2^i (k-i+1).
The inner sum over j is constant in j -- 2^(-j) * 2^(-(k-i-j)-1) = 2^(-(k-i)-1)
-- so it contributes a factor (k-i+1), and 2^k * 2^(-(k-i)-1) = 2^(i-1). -/
theorem E1k_bound (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    |E1k k| ≤ (1/2) * ∑ i ∈ Finset.range (k + 1),
      beta i * (2:ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1) := by
  sorry
