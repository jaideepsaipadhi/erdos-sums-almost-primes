/-- The r=2 dominator at constant 400, for the z-scaled terms. -/
theorem deriv2_bound_uniform_summable_five_z :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      400 * (Real.log ((p:ℕ):ℝ)) ^ 2 * (((p:ℕ):ℝ)) ^ (-(2:ℝ))) := by
  have h := deriv2_bound_uniform_summable_five.mul_left 2
  apply h.congr
  intro p
  ring
