/-- Each iterated derivative of a term is differentiable everywhere. -/
theorem iteratedDeriv_term_differentiable (s : ℝ) (n : ℕ) (hn : n ≠ 0) (j : ℕ) :
    Differentiable ℂ (fun w : ℂ => iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w) := by
  have heq : (fun w : ℂ => iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w)
      = fun w : ℂ => ((Nat.descFactorial (bigOmega n) j : ℕ) : ℂ) * w ^ (bigOmega n - j)
        * (((n:ℂ)) ^ (-(s:ℂ))) := by
    funext w
    exact iteratedDeriv_zOmega_term s n hn j w
  rw [heq]
  apply Differentiable.mul_const
  apply Differentiable.const_mul
  exact differentiable_pow _
