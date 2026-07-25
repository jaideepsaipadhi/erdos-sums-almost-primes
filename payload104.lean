theorem zOmega_factors_multipliable (s : ℝ) (hs : 1 < s) (z : ℂ) :
    Multipliable (fun p : Nat.Primes =>
      (1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))⁻¹) := by
  have hsum := zOmega_prime_sum_summable s hs z
  have hnn : ∀ p : Nat.Primes, (0:ℝ) ≤ Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) := by
    intro p
    positivity
  have hhalf : ∀ᶠ p in Filter.cofinite,
      Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) ≤ 1/2 := by
    have h := hsum.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
    filter_upwards [h] with p hp
    exact hp
  sorry
