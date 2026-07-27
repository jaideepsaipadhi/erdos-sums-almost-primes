/-- s-free version of the per-prime bound.  hasDerivAt_tsum_of_isPreconnected
needs a dominating function independent of the point, so we replace p^(-2s)
by p^(-2), valid since s >= 1 and p >= 3 > 1. -/
theorem deriv_prime_term_bound_uniform (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(-(z * (z - 1) * Real.log (p:ℝ))
        / ((((p:ℝ)) ^ s - 1) * (((p:ℝ)) ^ s - z)))|
      ≤ 27 * Real.log (p:ℝ) * ((p:ℝ)) ^ (-(2:ℝ)) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hlogpos : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hbase := deriv_prime_term_bound p hp s hs z hz
  have hmono : ((p:ℝ)) ^ (-2*s) ≤ ((p:ℝ)) ^ (-(2:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have : 27 * Real.log (p:ℝ) * ((p:ℝ)) ^ (-2*s)
      ≤ 27 * Real.log (p:ℝ) * ((p:ℝ)) ^ (-(2:ℝ)) := by
    apply mul_le_mul_of_nonneg_left hmono
    linarith
  linarith

/-- The s-free dominator is summable. -/
theorem deriv_bound_uniform_summable :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      27 * Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-(2:ℝ))) := by
  have h := deriv_series_summable 1 (le_refl 1)
  have heq : (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-2*(1:ℝ)))
      = fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)) ^ (-(2:ℝ)) := by
    funext p
    norm_num
  rw [heq] at h
  have h27 := h.mul_left 27
  apply h27.congr
  intro p
  ring
