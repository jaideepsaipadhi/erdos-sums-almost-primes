/-- s-free dominator for the correction series at p >= 5, for the
s-continuity argument. -/
theorem correction_bound_uniform_summable_five :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      18 * (((p:ℕ):ℝ)) ^ (-(2:ℝ))) := by
  have h2 : (-(2:ℝ)) < -1 := by norm_num
  have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2:ℝ))) :=
    Real.summable_nat_rpow.mpr h2
  exact (hbase.subtype _).mul_left 18

/-- The correction bound, s-free: 18 p^(-2s) <= 18 p^(-2) for s >= 1. -/
theorem correction_bound_sfree (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm ((-Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ)))
        + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-s)) : ℝ) : ℂ))
      ≤ 18 * (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := by
  have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp
  have hbase := prime_correction_bound_complex p hp s hs z hz
  have hmono : (((p:ℕ):ℝ)) ^ (-2*s) ≤ (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  linarith
