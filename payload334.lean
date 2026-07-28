theorem hasDerivAt_clog_series2 (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
          / ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
          / ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - z)))
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (z * ((z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) ^ 2
            * (((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)
            * ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z
              + ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
          / (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
            * (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))))) s := by
  have hy0 : (3/2 : ℝ) ∈ Set.Ioo (1:ℝ) 2 := by
    constructor <;> norm_num
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun (p : {p : ℕ // p.Prime ∧ 5 ≤ p}) (t : ℝ) =>
      -(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
        / ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - z))
    (g' := fun (p : {p : ℕ // p.Prime ∧ 5 ≤ p}) (t : ℝ) =>
      z * ((z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) ^ 2
          * (((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ)
          * ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - z
            + ((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1))
        / (((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1) ^ 2
          * (((((((p:ℕ):ℝ)) ^ t : ℝ) : ℂ) - z) ^ 2))))
    deriv2_bound_uniform_summable_five_z isOpen_Ioo isPreconnected_Ioo
    _ _ hy0 (deriv2_series_summable_at_basepoint z hz) hsmem
  · intro p y hy
    exact deriv2_clog_prime_term_z (p:ℕ) (by omega) y (le_of_lt hy.1) z hz
  · intro p y hy
    exact deriv2_clog_term_bound_z (p:ℕ) (by omega) y (le_of_lt hy.1) z hz
