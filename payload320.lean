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
  unfold E1k
  rw [Dk_eq_triple_sum k hk beta hbeta0 hderiv hbnd M0 hM00 hM0]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ k)]
  have hstep : |∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
      (∫ s in Set.Ioc (1:ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))|
      ≤ ∑ i ∈ Finset.range (k + 1),
          ((k : ℝ) - (i : ℝ) + 1) * (beta i * (1 / (2:ℝ) ^ ((k - i) + 1))) := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply Finset.sum_le_sum
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    rw [← inner_sum_const k i hik (beta i)]
    apply Finset.sum_le_sum
    intro j _
    exact Dk_term_bound i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbnd i)
      M0 hM00 hM0
  apply le_trans (mul_le_mul_of_nonneg_left hstep (by positivity))
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : (2:ℝ) ^ k * (1 / (2:ℝ) ^ ((k - i) + 1)) = (2:ℝ) ^ i / 2 := by
    have hsplit : (2:ℝ) ^ k = (2:ℝ) ^ i * (2:ℝ) ^ (k - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, pow_succ]
    field_simp
    ring
  calc (2:ℝ) ^ k * (((k : ℝ) - (i : ℝ) + 1) * (beta i * (1 / (2:ℝ) ^ ((k - i) + 1))))
      = ((k : ℝ) - (i : ℝ) + 1) * beta i * ((2:ℝ) ^ k * (1 / (2:ℝ) ^ ((k - i) + 1))) := by ring
    _ = ((k : ℝ) - (i : ℝ) + 1) * beta i * ((2:ℝ) ^ i / 2) := by rw [hpow]
    _ = 1 / 2 * (beta i * (2:ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1)) := by ring
