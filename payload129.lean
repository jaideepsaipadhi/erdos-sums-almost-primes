    · have hprod1 : ∏ i ∈ Finset.range N, G i = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_range] at hN2
        have hnp : i ∉ {p : ℕ | p.Prime} := by
          simp only [Set.mem_setOf_eq]
          intro hprime
          have := hprime.two_le
          omega
        rw [hG, Set.mulIndicator_of_notMem hnp]
      rw [hprod1]
      have hx34 : Norm.norm z * ((2:ℝ) ^ (-s)) ≤ 3/4 := by
        have h2s : (2:ℝ) ^ (-s) ≤ (2:ℝ) ^ (-(1:ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          linarith
        have h2one : (2:ℝ) ^ (-(1:ℝ)) = 1/2 := by
          rw [Real.rpow_neg_one]
          norm_num
        calc Norm.norm z * ((2:ℝ) ^ (-s)) ≤ (3/2) * ((2:ℝ) ^ (-s)) :=
              mul_le_mul_of_nonneg_right hz (by positivity)
          _ ≤ (3/2) * (1/2) := by
              rw [←  h2one]
              exact mul_le_mul_of_nonneg_left h2s (by norm_num)
          _ = 3/4 := by norm_num
      have hxnn : (0:ℝ) ≤ Norm.norm z * ((2:ℝ) ^ (-s)) := by positivity
      have hinv1 : (1:ℝ) ≤ (1 - Norm.norm z * ((2:ℝ) ^ (-s)))⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) (by linarith)]
        linarith
      have hexp1 : (1:ℝ) ≤ Real.exp (2 * ∑' n : ℕ, Norm.norm z * ((n:ℝ) ^ (-s))) := by
        rw [Real.one_le_exp_iff]
        have hsummable_nat : Summable (fun n : ℕ => Norm.norm z * ((n:ℝ) ^ (-s))) := by
          have hb : Summable (fun n : ℕ => ((n:ℝ) ^ (-s))) := by
            rw [Real.summable_nat_rpow]
            linarith
          exact hb.mul_left _
        have : (0:ℝ) ≤ ∑' n : ℕ, Norm.norm z * ((n:ℝ) ^ (-s)) := by
          apply tsum_nonneg
          intro n
          positivity
        linarith
      nlinarith [hinv1, hexp1]
