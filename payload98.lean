/-- A1 step 2: for each N, the family is summable over N-smooth numbers. -/
theorem zOmega_smooth_summable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2:ℝ) ^ s) (N : ℕ) :
    Summable (fun m : N.smoothNumbers => Norm.norm (zOmegaHom s z m)) := by
  have hf1 : zOmegaHom s z 1 = 1 := map_one _
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      zOmegaHom s z (a * b) = zOmegaHom s z a * zOmegaHom s z b := by
    intro a b _
    exact map_mul _ a b
  have hprime : ∀ {p : ℕ}, p.Prime →
      Summable (fun n : ℕ => Norm.norm (zOmegaHom s z (p ^ n))) := by
    intro p hp
    exact zOmega_prime_summable s hs z hz hp
  exact (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hprime N).1
