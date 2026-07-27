/-- kappa(s)^z -> (1/2)^z as s -> 1 from above. -/
theorem kappa_cpow_tendsto (z : ℂ) :
    Filter.Tendsto (fun s : ℝ => ((kappaFac s : ℝ) : ℂ) ^ z)
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds ((((1/2 : ℝ)) : ℂ) ^ z)) := by
  have hk := kappaFac_tendsto_half
  have heq : ∀ s : ℝ, s ∈ Set.Ioi (1:ℝ) →
      ((kappaFac s : ℝ) : ℂ) ^ z = Complex.exp (z * ((Real.log (kappaFac s) : ℝ) : ℂ)) := by
    intro s hs
    exact ofReal_cpow_eq_exp (kappaFac s) (kappaFac_pos s hs (cFac_pos s hs)) z
  have hlog : Filter.Tendsto (fun s : ℝ => Real.log (kappaFac s))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (Real.log (1/2 : ℝ))) := by
    apply (Real.continuousAt_log (by norm_num)).tendsto.comp hk
  have hcomp : Filter.Tendsto (fun s : ℝ => Complex.exp (z * ((Real.log (kappaFac s) : ℝ) : ℂ)))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (Complex.exp (z * ((Real.log (1/2 : ℝ) : ℝ) : ℂ)))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    apply Filter.Tendsto.const_mul
    exact (Complex.continuous_ofReal.continuousAt).tendsto.comp hlog
  have hval : Complex.exp (z * ((Real.log (1/2 : ℝ) : ℝ) : ℂ)) = (((1/2 : ℝ)) : ℂ) ^ z :=
    (ofReal_cpow_eq_exp (1/2 : ℝ) (by norm_num) z).symm
  rw [← hval]
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (heq s hs).symm
