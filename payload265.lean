theorem hasDerivAt_log_series (z : ℝ) (hz : |z| ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (hconv : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      -Real.log (1 - z * (((p:ℕ):ℝ)) ^ (-(3/2:ℝ)))
        + z * Real.log (1 - (((p:ℕ):ℝ)) ^ (-(3/2:ℝ))))) :
    HasDerivAt (fun t : ℝ => ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-Real.log (1 - z * (((p:ℕ):ℝ)) ^ (-t))
          + z * Real.log (1 - (((p:ℕ):ℝ)) ^ (-t))))
      (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-(z * (z - 1) * Real.log ((p:ℕ):ℝ))
          / (((((p:ℕ):ℝ)) ^ s - 1) * ((((p:ℕ):ℝ)) ^ s - z)))) s := by
  have hy0 : (3/2 : ℝ) ∈ Set.Ioo (1:ℝ) 2 := by
    constructor <;> norm_num
  apply hasDerivAt_tsum_of_isPreconnected
    deriv_bound_uniform_summable isOpen_Ioo isPreconnected_Ioo _ _ hy0 hconv hsmem
  · intro p y hy
    exact deriv_log_prime_factor (p:ℕ) p.2.2 y (le_of_lt hy.1) z hz
  · intro p y hy
    rw [Real.norm_eq_abs]
    exact deriv_prime_term_bound_uniform (p:ℕ) p.2.2 y (le_of_lt hy.1) z hz
