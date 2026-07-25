theorem L2b_summand (k : ℕ) (s : ℝ) (hs : 1 < s) (n i : ℕ) (hin : i ≤ n) (hnk : n ≤ k) :
    (Nat.choose k n : ℂ) *
        ((Nat.choose n i : ℂ)
          * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
          * ((Nat.factorial (n - i) : ℂ) * ((((2:ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
        * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s)
      / (Nat.factorial k : ℂ)
      = gCoeff (k - n) s * ((((2:ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)
        * ((((-Real.log (s - 1)) ^ (k - (n - i) - (k - n))
            / (Nat.factorial (k - (n - i) - (k - n))) : ℝ)) : ℂ) := by
  have hidx : k - (n - i) - (k - n) = i := by omega
  rw [hidx]
  have hkfac : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have htri := choose_mul_choose_div_factorial k n i hnk hin
  rw [div_eq_iff hkfac]
  rw [htri]
  have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hfni : ((Nat.factorial (n - i) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  have hfkn : ((Nat.factorial (k - n) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - n))
  field_simp
  ring
