/-- Uniform bound on the j-th derivative of a term, over the ball of radius r0. -/
theorem iteratedDeriv_term_bound (s : ℝ) (hs : 1 < s) (r0 : ℝ) (hr00 : 0 < r0)
    (j : ℕ) (n : ℕ) (hn : n ≠ 0) (w : ℂ) (hw : Norm.norm w ≤ r0) :
    Norm.norm (iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w)
      ≤ ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n - j) * ((n:ℝ) ^ (-s)) := by
  rw [iteratedDeriv_zOmega_term s n hn j w]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnorm_n : Norm.norm (((n:ℂ)) ^ (-(s:ℂ))) = ((n:ℝ) ^ (-s)) := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, Complex.ofReal_re]
  rw [norm_mul, norm_mul, norm_pow, hnorm_n, Complex.norm_natCast]
  have hdesc : ((Nat.descFactorial (bigOmega n) j : ℕ) : ℝ) ≤ ((bigOmega n : ℕ) : ℝ) ^ j := by
    have h := Nat.descFactorial_le_pow (bigOmega n) j
    exact_mod_cast h
  have hwpow : Norm.norm w ^ (bigOmega n - j) ≤ r0 ^ (bigOmega n - j) := by
    apply pow_le_pow_left (norm_nonneg _) hw
  have hnn : (0:ℝ) ≤ ((n:ℝ) ^ (-s)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hnn
  apply mul_le_mul hdesc hwpow (by positivity) (by positivity)
