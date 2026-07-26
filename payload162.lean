/-- At a prime, the z-weighted hom is just z * p^(-s). -/
theorem zOmegaHom_prime (s : ℝ) (z : ℂ) {p : ℕ} (hp : p.Prime) :
    zOmegaHom s z p = z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ) := by
  have hp0 : (p:ℕ) ≠ 0 := hp.pos.ne'
  show (if (p:ℕ) = 0 then 0
    else z ^ (bigOmega (p:ℕ)) * (((p:ℕ) : ℂ) ^ (-(s:ℂ)))) = _
  rw [if_neg hp0]
  have hO : bigOmega (p:ℕ) = 1 := by
    have := bigOmega_prime_pow hp 1
    rwa [pow_one] at this
  rw [hO, pow_one]
  congr 1
  rw [←  Complex.ofReal_natCast, ←  Complex.ofReal_cpow (Nat.cast_nonneg p)]
  norm_cast
