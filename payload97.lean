  have hterm : ∀ n : ℕ,
      Norm.norm (zOmegaHom s z (p ^ n)) = (Norm.norm z * ((p:ℝ) ^ (-s))) ^ n := by
    intro n
    have hpn : (p:ℕ) ^ n ≠ 0 := pow_ne_zero n hp.pos.ne'
    have hppos : 0 < (p:ℕ) ^ n := Nat.pos_of_ne_zero hpn
    show Norm.norm (if (p:ℕ) ^ n = 0 then 0
      else z ^ (bigOmega ((p:ℕ) ^ n)) * ((((p:ℕ) ^ n : ℕ) : ℂ) ^ (-(s:ℂ)))) = _
    rw [if_neg hpn, bigOmega_prime_pow hp n, norm_mul, norm_pow]
    rw [Complex.norm_natCast_cpow_of_pos hppos]
    rw [Complex.neg_re, Complex.ofReal_re]
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast ((p:ℝ)) n, ← Real.rpow_mul (Nat.cast_nonneg p)]
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((p:ℝ) ^ (-s)) n, ← Real.rpow_mul (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    ring_nf
  rw [Summable.congr _ (fun n => (hterm n).symm)]
  exact summable_geometric_of_lt_one (by positivity) hratio
