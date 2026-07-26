/-- Wide-radius variant (||z|| <= 5/2). -/
theorem prime_factor_sub_one_summable_complex_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 5/2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 40 * (p:ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (40:ℝ) * (p:ℝ) ^ (-2*s) =
        40 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 40
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      prime_factor_sub_one_bound_complex_wide (p:ℕ) p.property.2 s hs z hz)
    hcomp

/-- Wide-radius variant (||z|| <= 5/2). -/
theorem prime_factor_multipliable_complex_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 5/2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable_complex_wide s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + (Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
          (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
        1 + (Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1) := by
    intro p
    have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
    rw [prime_factor_eq_exp_complex (p:ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult
