  have hpos : ∀ᶠ p in Filter.cofinite,
      (0:ℝ) < (1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))⁻¹ := by
    filter_upwards [hhalf] with p hp
    apply inv_pos.mpr
    linarith
  have hlogsum : Summable (fun p : Nat.Primes =>
      Real.log ((1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))⁻¹)) := by
    have hbound : ∀ᶠ p in Filter.cofinite,
        Norm.norm (Real.log ((1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))⁻¹))
          ≤ 2 * (Norm.norm z * (((p:ℕ):ℝ) ^ (-s))) := by
      filter_upwards [hhalf] with p hp
      have hx0 : (0:ℝ) ≤ Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) := hnn p
      have hone : (0:ℝ) < 1 - Norm.norm z * (((p:ℕ):ℝ) ^ (-s)) := by linarith
      rw [Real.log_inv, Real.norm_eq_abs, abs_neg,
        abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
      exact neg_log_one_sub_le _ hx0 hp
    have hsum2 : Summable (fun p : Nat.Primes =>
        2 * (Norm.norm z * (((p:ℕ):ℝ) ^ (-s)))) := hsum.mul_left 2
    exact Summable.of_norm_bounded_eventually hsum2 hbound
  exact Real.multipliable_of_summable_log' hpos hlogsum
