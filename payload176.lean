/-- The j-th derivative of a single term. -/
theorem iteratedDeriv_zOmega_term (s : ℝ) (n : ℕ) (hn : n ≠ 0) (j : ℕ) (w : ℂ) :
    iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w
      = ((Nat.descFactorial (bigOmega n) j : ℕ) : ℂ) * w ^ (bigOmega n - j)
        * (((n:ℂ)) ^ (-(s:ℂ))) := by
  have hterm : (fun z : ℂ => zOmegaHom s z n)
      = fun z : ℂ => z ^ (bigOmega n) * (((n:ℂ)) ^ (-(s:ℂ))) := by
    funext z
    show (if n = 0 then 0 else z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s:ℂ)))) = _
    rw [if_neg hn]
  rw [hterm, iteratedDeriv_mul_const_field, iteratedDeriv_pow]
  ring
