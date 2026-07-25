      have hsummable_nat : Summable (fun n : ℕ => Norm.norm z * ((n:ℝ) ^ (-s))) := by
        have hb : Summable (fun n : ℕ => ((n:ℝ) ^ (-s))) := by
          rw [Real.summable_nat_rpow]
          linarith
        exact hb.mul_left _
      have hnn_nat : ∀ n : ℕ, (0:ℝ) ≤ Norm.norm z * ((n:ℝ) ^ (-s)) := by
        intro n
        positivity
      calc ∏ i ∈ (Finset.range N).erase 2, G i
          ≤ ∏ i ∈ (Finset.range N).erase 2,
              Real.exp (2 * (Norm.norm z * ((i:ℝ) ^ (-s)))) := by
            apply finset_prod_le_prod_nonneg
            · intro i _
              exact hGnn i
            · intro i hi
              have hi2 : i ≠ 2 := (Finset.mem_erase.mp hi).1
              have hiN : i ∈ Finset.range N := (Finset.mem_erase.mp hi).2
              exact hGle i hiN hi2
        _ = Real.exp (∑ i ∈ (Finset.range N).erase 2,
              2 * (Norm.norm z * ((i:ℝ) ^ (-s)))) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp (2 * ∑' n : ℕ, Norm.norm z * ((n:ℝ) ^ (-s))) := by
            apply Real.exp_le_exp.mpr
            rw [←  Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
            exact hsummable_nat.sum_le_tsum _ (fun i _ => hnn_nat i)
