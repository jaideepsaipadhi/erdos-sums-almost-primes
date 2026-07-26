theorem omega_pow_summable_radius (s : ℝ) (hs : 1 < s) (j : ℕ)
    (r0 r : ℝ) (hr00 : 0 < r0) (hr0r : r0 < r)
    (hr0 : 0 ≤ r) (hr3 : r * ((3:ℝ) ^ (-s)) ≤ 1/2) (hr2 : r < (2:ℝ) ^ s) :
    Summable (fun n : ℕ =>
      ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n) * ((n:ℝ) ^ (-s))) := by
  have hratio : 1 < r / r0 := (one_lt_div hr00).mpr hr0r
  obtain ⟨ C, hCpos, hC ⟩ := pow_le_const_mul_geom j hratio
  have hbig : Summable (fun n : ℕ => Norm.norm (zOmegaHom s ((r:ℝ) : ℂ) n)) := by
    apply zOmega_summable_radius s hs r hr0 hr3 hr2
    rw [Complex.norm_real, abs_of_nonneg hr0]
  have hscaled : Summable (fun n : ℕ => C * Norm.norm (zOmegaHom s ((r:ℝ) : ℂ) n)) :=
    hbig.mul_left C
  apply Summable.of_nonneg_of_le _ _ hscaled
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp [bigOmega]
      positivity
    · have hnorm : Norm.norm (zOmegaHom s ((r:ℝ) : ℂ) n)
          = r ^ (bigOmega n) * ((n:ℝ) ^ (-s)) := by
        rw [zOmegaHom_norm s _ hn, Complex.norm_real, abs_of_nonneg hr0]
      rw [hnorm]
      have hkey : ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n)
          ≤ C * r ^ (bigOmega n) := by
        have h1 := hC (bigOmega n)
        have hr0pow : (0:ℝ) < r0 ^ (bigOmega n) := by positivity
        calc ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n)
            ≤ (C * (r / r0) ^ (bigOmega n)) * r0 ^ (bigOmega n) := by
              apply mul_le_mul_of_nonneg_right h1 (le_of_lt hr0pow)
          _ = C * r ^ (bigOmega n) := by
              rw [div_pow]
              field_simp
      have hnn : (0:ℝ) ≤ ((n:ℝ) ^ (-s)) := by positivity
      calc ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n) * ((n:ℝ) ^ (-s))
          ≤ (C * r ^ (bigOmega n)) * ((n:ℝ) ^ (-s)) := by
            apply mul_le_mul_of_nonneg_right hkey hnn
        _ = C * (r ^ (bigOmega n) * ((n:ℝ) ^ (-s))) := by ring
