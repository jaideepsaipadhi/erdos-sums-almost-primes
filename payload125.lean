    have hprimes_sum : Summable (fun p : Nat.Primes => Norm.norm z * ((p:ℝ) ^ (-s))) :=
      zOmega_prime_sum_summable s hs z
    have hGle : ∀ i ∈ Finset.range N, i ≠ 2 →
        G i ≤ Real.exp (2 * (Norm.norm z * ((i:ℝ) ^ (-s)))) := by
      intro i _ hi2
      rw [hG]
      by_cases hp : i ∈ {p : ℕ | p.Prime}
      · rw [Set.mulIndicator_of_mem hp]
        have hprime : i.Prime := hp
        have hi3 : 3 ≤ i := by
          have h2 : 2 ≤ i := hprime.two_le
          omega
        apply inv_one_sub_le_exp
        · positivity
        · exact zOmega_half_of_three_le s hs z hz hi3
      · rw [Set.mulIndicator_of_notMem hp]
        have : (0:ℝ) ≤ 2 * (Norm.norm z * ((i:ℝ) ^ (-s))) := by positivity
        calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
          _ ≤ Real.exp (2 * (Norm.norm z * ((i:ℝ) ^ (-s)))) := Real.exp_le_exp.mpr this
    sorry
