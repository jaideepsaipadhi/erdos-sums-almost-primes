/-- Per-term bound for S_2: the j-th term is at most 2^(-j) 2^(-l-1).
Uses 2^(-js) <= 2^(-j) on [1,2] and the exact integral
integral_log_pow_sub_one. -/
theorem S2_term_le (l j : ℕ) :
    (∫ s in Set.Ioc (1:ℝ) 2,
      (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
        * (2:ℝ) ^ (-(j:ℝ) * s))
      ≤ (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ (l + 1)) := by
  have hleft := integrable_S2_integrand l j
  have hright := (integrable_log_pow_sub_one l).const_mul ((2:ℝ) ^ (-(j:ℝ)))
  have hL : ∀ s : ℝ, s ∈ Set.Ioc (1:ℝ) 2 →
      (0:ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) := by
    intro s hs
    apply mul_nonneg _ (by linarith [hs.1])
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
  have hnn : (0:ℝ → ℝ) ≤ (0:ℝ → ℝ) := le_refl _
  have hmono : (∫ s in Set.Ioc (1:ℝ) 2,
        (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
          * (2:ℝ) ^ (-(j:ℝ) * s))
      ≤ ∫ s in Set.Ioc (1:ℝ) 2,
        (2:ℝ) ^ (-(j:ℝ)) * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hright ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have h2 : (0:ℝ) < (2:ℝ) ^ (-(j:ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
      exact mul_nonneg (hL s hs) (le_of_lt h2)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hmonoexp : (2:ℝ) ^ (-(j:ℝ) * s) ≤ (2:ℝ) ^ (-(j:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hj : (0:ℝ) ≤ (j:ℝ) := by positivity
        nlinarith [hs.1]
      calc (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) * (2:ℝ) ^ (-(j:ℝ) * s)
          ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) * (2:ℝ) ^ (-(j:ℝ)) :=
            mul_le_mul_of_nonneg_left hmonoexp (hL s hs)
        _ = (2:ℝ) ^ (-(j:ℝ))
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by ring
  rw [MeasureTheory.integral_const_mul, integral_log_pow_sub_one] at hmono
  exact hmono
