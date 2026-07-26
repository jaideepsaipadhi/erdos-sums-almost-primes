/-- All iterated derivatives of the n = 0 term vanish. -/
theorem iteratedDeriv_term_zero (s : ℝ) (j : ℕ) (w : ℂ) :
    iteratedDeriv j (fun z : ℂ => zOmegaHom s z 0) w = 0 := by
  have hz : (fun z : ℂ => zOmegaHom s z 0) = fun _ : ℂ => (0:ℂ) := by
    funext z
    exact map_zero _
  rw [hz]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp
  · rw [iteratedDeriv_const_of_ne (by omega)]
