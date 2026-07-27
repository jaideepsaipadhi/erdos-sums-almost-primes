/-- MANUSCRIPT LEMMA 3.9 (complex z): G2^(1,0) = z * G2 * c(s,z), with
  c(s,z) = log 2/(2^s - 1) + f(s) - sum_{p>=3} (z-1) log p/((p^s-1)(p^s-z)).
Stated in the multiplied form the manuscript's section 3.5 uses (G2^(1,0) =
z G2 c), not the logarithmic one -- that avoids Complex.log of the product,
which branch cuts would break.

f is a hypothesis, as in lemma_3_9_real: the manuscript certifies it
numerically from FLINT Stieltjes constants rather than expanding it. -/
theorem lemma_3_9_complex (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ => G2manu t z)
      (G2manu s z *
        (z * (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)
          + ((-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
              / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
            + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                  / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                    / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))))) s := by
  have hkap := hasDerivAt_kappa_cpow z s hsmem f hf
  have hg2c := hasDerivAt_G2C z hz s hsmem
  have hmul := hkap.mul hg2c
  have hfun : (fun t : ℝ => G2manu t z)
      = ((fun t : ℝ => ((kappaFac t : ℝ) : ℂ) ^ z) * fun t : ℝ => G2C t z) := by
    funext t
    simp only [Pi.mul_apply]
    unfold G2manu
    ring
  rw [hfun]
  have hval : G2manu s z *
      (z * (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)
        + ((-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
            / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
              / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))))
      = ((kappaFac s : ℝ) : ℂ) ^ z
          * (z * (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)) * G2C s z
        + ((kappaFac s : ℝ) : ℂ) ^ z
          * (G2C s z *
            ((-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
                / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
              + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                  (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                    / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                      / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)))) := by
    unfold G2manu
    ring
  rw [hval]
  exact hmul
