/-- A1 step 4c: the sum of norms over N-smooth numbers equals the partial
Euler product over primes below N. -/
theorem zOmegaNorm_smooth_hasSum (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) (N : ℕ) :
    HasSum (fun m : N.smoothNumbers => zOmegaNormHom s z m)
      (∏ p ∈ N.primesBelow, ∑' n : ℕ, zOmegaNormHom s z (p ^ n)) := by
  have hf1 : zOmegaNormHom s z 1 = 1 := map_one _
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      zOmegaNormHom s z (a * b) = zOmegaNormHom s z a * zOmegaNormHom s z b := by
    intro a b _
    exact map_mul _ a b
  have hprime : ∀ {p : ℕ}, p.Prime →
      Summable (fun n : ℕ => Norm.norm (zOmegaNormHom s z (p ^ n))) := by
    intro p hp
    have h := zOmega_prime_summable s hs z hz hp
    apply h.congr
    intro n
    rw [zOmegaNormHom_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hprime N).2
