/-- Double Leibniz for Fbig in the MANUSCRIPT normalisation.
Parallel to iteratedDeriv_Fbig; factor A is (s-1)^(-z) and factor C is G2manu,
so the coefficients that emerge are (-log(s-1))^l / l! as in Lemma 2.2. -/
theorem iteratedDeriv_Fbig_manu (k : ℕ) (s : ℝ) (hs : 1 < s) (hc : 0 < cFac s) :
    iteratedDeriv k (fun z => Fbig s z) 0
      = ∑ n ∈ Finset.range (k + 1),
          (Nat.choose k n : ℂ) *
            (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℂ)
                * iteratedDeriv i (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) 0
                * iteratedDeriv (n - i) (fun w : ℂ => (1 - w / ((2:ℂ) ^ (s:ℂ)))⁻¹) 0)
            * iteratedDeriv (k - n) (fun w : ℂ => G2manu s w) 0 := by
  have hs1 : (1:ℝ) ≤ s := le_of_lt hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hk : (0:ℝ) < kappaFac s := kappaFac_pos s hs hc
  have hzne : 1 - (0:ℂ) / ((2:ℂ) ^ (s:ℂ)) ≠ 0 := by
    simp
  have hA : ∀ j : ℕ, ContDiffAt ℂ j
      (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) 0 :=
    fun j => contDiffAt_factorAmanu s hsm1 j 0
  have hB : ∀ j : ℕ, ContDiffAt ℂ j
      (fun w : ℂ => (1 - w / ((2:ℂ) ^ (s:ℂ)))⁻¹) 0 :=
    fun j => contDiffAt_factorB s j 0 hzne
  have hC : ∀ j : ℕ, ContDiffAt ℂ j (fun w : ℂ => G2manu s w) 0 :=
    fun j => contDiffAt_factorCmanu s hs1 hk j
  have hAB : ∀ j : ℕ, ContDiffAt ℂ j
      ((fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w))
        * (fun w : ℂ => (1 - w / ((2:ℂ) ^ (s:ℂ)))⁻¹)) 0 :=
    fun j => (hA j).mul (hB j)
  rw [Fbig_eq_prod_manu s hs hc]
  rw [iteratedDeriv_mul (hAB k) (hC k)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_mul (hA n) (hB n)]
  try rw [Finset.sum_mul]
  try rw [Finset.mul_sum]
  try rw [Finset.sum_mul]
  try apply Finset.sum_congr rfl
  try intro i _
  try ring
