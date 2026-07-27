/-- MANUSCRIPT section 3.5: |E_1(k)| <= alpha_+ (k+1).
From (10), since (k-i+1) <= (k+1) for every i in the sum.  alpha_+ bounds
(1/2) sum_{i<=k} beta_i 2^i uniformly in k -- the manuscript evaluates it by
splitting at 30 and using the Cauchy tail beta_i <= M1/2.9^i, which is a
certified computation, so it enters here as a hypothesis. -/
theorem E1k_le_alpha (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0)
    (alpha : ℝ) (halpha : ∀ m : ℕ,
      (1/2) * ∑ i ∈ Finset.range (m + 1), beta i * (2:ℝ) ^ i ≤ alpha) :
    |E1k k| ≤ alpha * ((k : ℝ) + 1) := by
  have hb := E1k_bound k hk beta hbeta0 hderiv hbnd M0 hM00 hM0
  have hstep : (1/2) * ∑ i ∈ Finset.range (k + 1),
        beta i * (2:ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1)
      ≤ ((k : ℝ) + 1) * ((1/2) * ∑ i ∈ Finset.range (k + 1), beta i * (2:ℝ) ^ i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hikR : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
    have hi0 : (0:ℝ) ≤ (i : ℝ) := by positivity
    have hnn : (0:ℝ) ≤ beta i * (2:ℝ) ^ i := by
      apply mul_nonneg (hbeta0 i)
      positivity
    have hfac : (k : ℝ) - (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by linarith
    nlinarith [hnn, hfac]
  calc |E1k k| ≤ (1/2) * ∑ i ∈ Finset.range (k + 1),
        beta i * (2:ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1) := hb
    _ ≤ ((k : ℝ) + 1) * ((1/2) * ∑ i ∈ Finset.range (k + 1),
        beta i * (2:ℝ) ^ i) := hstep
    _ ≤ ((k : ℝ) + 1) * alpha := by
        apply mul_le_mul_of_nonneg_left (halpha k)
        positivity
    _ = alpha * ((k : ℝ) + 1) := by ring
