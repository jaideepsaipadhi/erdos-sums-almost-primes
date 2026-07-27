/-- d/ds G2C = G2C * (per-prime sum over p >= 3), assembling the p = 3 factor
and the p >= 5 tail by the product rule.  The p = 3 term appears separately
because G2C splits it out; combining gives the full p >= 3 sum of Lemma 3.9. -/
theorem hasDerivAt_G2C (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ => G2C t z)
      (G2C s z *
        ((-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
            / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
              / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)))) s := by
  have h3 := hasDerivAt_prime_three_factor z hz s hsmem
  have htail := hasDerivAt_G2tailC z hz s hsmem
  have hcast : ∀ t : ℝ, ((((3:ℕ):ℝ)) ^ (-t) : ℝ) = (((3:ℝ)) ^ (-t) : ℝ) := by
    intro t
    norm_num
  simp only [hcast] at h3
  have hmul := h3.mul htail
  have hG2C : ∀ t : ℝ, G2C t z
      = ((1 - z * ((((3:ℝ)) ^ (-t) : ℝ) : ℂ))⁻¹
          * (((1 - ((3:ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z) * G2tailC t z := by
    intro t
    unfold G2C
    ring
  simp only [hG2C]
  convert hmul using 1
  rw [hG2C s]
  ring
