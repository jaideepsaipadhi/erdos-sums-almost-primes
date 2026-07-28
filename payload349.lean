/-- MANUSCRIPT Theorem 6.1: A^(2)_m <= (m+1)/2.
Each term of S_2(m) is at most 2^(-j) 2^(-(m-j)-1) = 2^(-m-1), constant in j;
there are m+1 of them, and multiplying by 2^m gives (m+1)/2. -/
theorem A2m_le (m : ℕ) : A2m m ≤ ((m : ℝ) + 1) / 2 := by
  have hbound : S2m m ≤ ∑ j ∈ Finset.range (m + 1),
      (1:ℝ) * (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ ((m - j) + 1)) := by
    unfold S2m
    apply Finset.sum_le_sum
    intro j _
    have h := S2_term_le (m - j) j
    calc (∫ s in Set.Ioc (1:ℝ) 2,
          (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (s - 1)
            * (2:ℝ) ^ (-(j:ℝ) * s))
        ≤ (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ ((m - j) + 1)) := h
      _ = (1:ℝ) * (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ ((m - j) + 1)) := by ring
  have hconst := inner_sum_const m 0 (Nat.zero_le m) (1:ℝ)
  simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at hconst
  rw [hconst] at hbound
  unfold A2m
  have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have hstep : (2:ℝ) ^ m * S2m m
      ≤ (2:ℝ) ^ m * (((m : ℝ) + 1) * ((1:ℝ) * (1 / (2:ℝ) ^ (m + 1)))) :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt h2m)
  have hval : (2:ℝ) ^ m * (((m : ℝ) + 1) * ((1:ℝ) * (1 / (2:ℝ) ^ (m + 1))))
      = ((m : ℝ) + 1) / 2 := by
    rw [pow_succ]
    field_simp
    ring
  linarith [hstep, hval]
