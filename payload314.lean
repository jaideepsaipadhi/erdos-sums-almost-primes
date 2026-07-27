/-- The Ik side as a triangular double sum of integrals. -/
theorem Ik_eq_double_sum (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    Ik k = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
      (∫ s in Set.Ioc (1:ℝ) 2,
        (gManu i s).re * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
  unfold Ik
  have hpt : ∀ s ∈ Set.Ioc (1:ℝ) 2, Fk k s
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (gManu i s).re * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))) := by
    intro s hs
    rw [Fk_expansion_manu k hk s hs.1 hs.2]
    exact triangular_sum_comm k (fun p q =>
      (gManu q s).re * (2:ℝ) ^ (-(p:ℝ) * s)
        * ((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q))))
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_finset_sum]
    intro j _
    exact integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbound i)
      M0 hM00 hM0
  · intro i _
    apply MeasureTheory.integrable_finset_sum
    intro j _
    exact integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbound i)
      M0 hM00 hM0
