/-- The k-th derivative at 0 of a single term, in collapsed form. -/
theorem iteratedDeriv_term_at_zero (s : ℝ) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    iteratedDeriv k (fun z : ℂ => zOmegaHom s z n) 0
      = if bigOmega n = k then (Nat.factorial k : ℂ) * (((n:ℂ)) ^ (-(s:ℂ))) else 0 := by
  by_cases hn : n = 0
  · subst hn
    rw [iteratedDeriv_term_zero s k 0]
    have hO : bigOmega 0 ≠ k := by
      have : bigOmega 0 = 0 := by unfold bigOmega; simp
      omega
    rw [if_neg hO]
  · have hterm : (fun z : ℂ => zOmegaHom s z n)
        = fun z : ℂ => z ^ (bigOmega n) * (((n:ℂ)) ^ (-(s:ℂ))) := by
      funext z
      show (if n = 0 then 0 else z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s:ℂ)))) = _
      rw [if_neg hn]
    rw [hterm, iteratedDeriv_monomial_zero]
