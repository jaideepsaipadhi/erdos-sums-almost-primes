/-- Complex per-prime term of Lemma 3.9:
d/ds [-Complex.log(1 - z p^(-s)) + z Complex.log(1 - p^(-s))]
  = -z(z-1) log p / ((p^s - 1)(p^s - z)).
Complex analogue of deriv_log_prime_factor; the cancellation between the two
logs is again what produces the p^(-2s) decay. -/
theorem deriv_clog_prime_factor (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * Complex.log (1 - (((((p:ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)))
      (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)) s := by
  have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
  have hps : (3:ℝ) ≤ (((p:ℕ):ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p:ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hneg : (((p:ℕ):ℝ)) ^ (-s) = ((((p:ℕ):ℝ)) ^ s)⁻¹ := Real.rpow_neg (le_of_lt hp0) s
  have hone : Norm.norm (1 : ℂ) ≤ 2 := by simp; norm_num
  have hA := (deriv_clog_one_sub_const_rpow p hp s hs z hz).neg
  have hB := (deriv_clog_one_sub_const_rpow p hp s hs 1 hone).const_mul z
  simp only [one_mul] at hB
  have hsum := hA.add hB
  have hslitz := Complex.slitPlane_ne_zero (one_sub_mem_slitPlane p hp s hs z hz)
  have hslit1 := Complex.slitPlane_ne_zero (one_sub_mem_slitPlane p hp s hs 1 hone)
  simp only [one_mul] at hslit1
  have hpsC : (((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro hcon
    rw [hcon] at hps
    linarith
  have hval : -(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)
      = -(z * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ)
            * ((((((p:ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
            / (1 - z * (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ)))
        + z * (((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ)
            * ((((((p:ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
            / (1 - (((((p:ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))) := by
    rw [hneg]
    push_cast
    rw [show (1 : ℂ) - z * ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ))⁻¹
        = (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)) - z) / ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)) by
      field_simp]
    rw [show (1 : ℂ) - ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ))⁻¹
        = (((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)) - 1) / ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ)) by
      field_simp]
    field_simp
    ring
  rw [hval]
  exact hsum
