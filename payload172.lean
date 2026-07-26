/-- The norm of the z-weighted term at any n. -/
theorem zOmegaHom_norm (s : ℝ) (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    Norm.norm (zOmegaHom s z n) = Norm.norm z ^ (bigOmega n) * ((n:ℝ) ^ (-s)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  show Norm.norm (if n = 0 then 0
    else z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s:ℂ)))) = _
  rw [if_neg hn, norm_mul, norm_pow]
  congr 1
  rw [Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, Complex.ofReal_re]
