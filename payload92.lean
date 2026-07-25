theorem coeff_Fbig_eq_convolution (k : ℕ) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
    (iteratedDeriv k (fun z => Fbig s z) 0) / (Nat.factorial k : ℂ)
      = ∑ p ∈ Finset.range (k + 1),
          ∑ q ∈ Finset.range (k - p + 1),
            gCoeff q s * (((2:ℝ) ^ (-(p:ℝ) * s) : ℝ) : ℂ)
              * ((((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ) := by
  have hAval : ∀ i : ℕ,
      iteratedDeriv i (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) 0
        = (Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ) := by
    intro i
    have h := coeff_pow_neg s hs i
    have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    field_simp at h
    linear_combination h
  have hBval : ∀ j : ℕ,
      iteratedDeriv j (fun w : ℂ => (1 - w / ((2:ℂ) ^ (s:ℂ)))⁻¹) 0
        = (Nat.factorial j : ℂ) * ((((2:ℝ) ^ (-(j:ℝ) * s) : ℝ)) : ℂ) := by
    intro j
    have h := coeff_geom s hs j
    have hfj : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    field_simp at h
    linear_combination h
  have hCval : ∀ q : ℕ,
      iteratedDeriv q (fun w : ℂ => G2C s w) 0 = (Nat.factorial q : ℂ) * gCoeff q s := by
    intro q
    unfold gCoeff
    have hfq : ((Nat.factorial q : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
    field_simp
  rw [iteratedDeriv_Fbig k s hs]
  simp only [hAval, hBval, hCval]
  rw [Finset.sum_div]
  rw [leibniz_flatten k (fun n i => (Nat.choose k n : ℂ) *
    ((Nat.choose n i : ℂ)
      * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
      * ((Nat.factorial (n - i) : ℂ) * ((((2:ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
    * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s) / (Nat.factorial k : ℂ))]
  rw [conv_flatten k (fun p q => gCoeff q s * (((2:ℝ) ^ (-(p:ℝ) * s) : ℝ) : ℂ)
    * ((((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ))]
  apply sigma_reindex
  intro n i hin hnk
  exact L2b_summand k s hs n i hin hnk
