  have hcof : ∀ᶠ p : Nat.Primes, Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) ≤ 1/2 := by
    sorry
  have hlogbound : ∀ᶠ p : Nat.Primes,
      Norm.norm (Real.log ((1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))⁻¹))
        ≤ 2 * (Norm.norm z * (((p:ℕ):ℝ) ^ (-s))) := by
    filter_upwards [hcof] with p hp
    have hx0 : (0:ℝ) ≤ Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) := by positivity
    have hone : (0:ℝ) < 1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) := by linarith
    rw [Real.log_inv, norm_neg, Real.norm_eq_abs,
      abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
    have hkey : -Real.log (1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))
        ≤ 2 * (Norm.norm z * (((p:ℕ):ℝ) ^ (-s))) := by
      nlinarith [Real.add_one_le_exp (-(Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))),
        Real.log_le_sub_one_of_pos hone, hx0, hp]
    linarith
  have hsum2 : Summable (fun p : Nat.Primes => 2 * (Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))) :=
    (zOmega_prime_sum_summable s hs z).mul_left 2
  exact Summable.of_norm_bounded_eventually hsum2 hlogbound
