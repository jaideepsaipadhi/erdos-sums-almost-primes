/-- Per-term bound for (10): each triple-sum term is at most
beta_i * 2^(-j) * 2^(-l-1). -/
theorem Dk_term_bound (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    |∫ s in Set.Ioc (1:ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))|
      ≤ beta * (2:ℝ) ^ (-(j:ℝ)) * (1 / (2:ℝ) ^ (l + 1)) := by
  have hdom := (integrable_log_pow_sub_one l).const_mul (beta * (2:ℝ) ^ (-(j:ℝ)))
  have hae : ∀ᵐ s ∂ (MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) 2)),
      Norm.norm (((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
        ≤ beta * (2:ℝ) ^ (-(j:ℝ))
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
    have hIoo : (MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) 2))
        (Set.Ioc (1:ℝ) 2 \ Set.Ioo (1:ℝ) 2) = 0 := by
      have : Set.Ioc (1:ℝ) 2 \ Set.Ioo (1:ℝ) 2 ⊆ {(2:ℝ)} := by
        intro x hx
        simp only [Set.mem_diff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff] at hx ⊢
        rcases hx with ⟨ ⟨ h1, h2 ⟩, h3 ⟩
        by_contra hne
        exact h3 ⟨ h1, lt_of_le_of_ne h2 hne ⟩
      exact MeasureTheory.measure_mono_null this (by simp)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      MeasureTheory.compl_mem_ae_iff.mpr hIoo] with s hs hs2
    have hsIoo : s ∈ Set.Ioo (1:ℝ) 2 := by
      by_contra hcon
      exact hs2 (Set.mem_diff_of_mem hs hcon)
    rw [Real.norm_eq_abs]
    exact Dk_integrand_ptwise i j l beta hbeta0 hderiv hbnd M0 hM00 hM0 s hsIoo
  have hle := MeasureTheory.norm_integral_le_of_norm_le hdom hae
  rw [Real.norm_eq_abs] at hle
  rw [MeasureTheory.integral_const_mul, integral_log_pow_sub_one] at hle
  exact hle
