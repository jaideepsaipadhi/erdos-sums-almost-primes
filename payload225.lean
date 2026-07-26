/-- kappa(s) = (s-1) cFac s tends to 1/2 as s -> 1 from above.
This is the limit that section 3.5's mean value step needs, and the reason
G2(1,z) = 2^(-z) prod_{p>2}(...) has the 2^(-z) prefactor. -/
theorem kappaFac_tendsto_half :
    Filter.Tendsto kappaFac (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (1/2 : ℝ)) := by
  rw [← Filter.tendsto_ofReal_iff]
  have hres : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds 1) :=
    zeta_residue_halfplane.comp ofReal_tendsto_halfplane
  have htwo : Filter.Tendsto (fun s : ℝ => 1 - ((2:ℂ)) ^ (-(s:ℂ)))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (1/2 : ℂ)) := by
    have hcont : ContinuousAt (fun s : ℝ => 1 - ((2:ℂ)) ^ (-(s:ℂ))) 1 := by
      apply ContinuousAt.sub continuousAt_const
      apply ContinuousAt.const_cpow
      · exact (Complex.continuous_ofReal.continuousAt).neg
      · left; norm_num
    have hval : (fun s : ℝ => 1 - ((2:ℂ)) ^ (-(s:ℂ))) 1 = (1/2 : ℂ) := by
      norm_num
      rw [show (-(1:ℂ)) = ((-1 : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
      rw [Real.rpow_neg_one]
      norm_num
    rw [← hval]
    exact hcont.continuousWithinAt
  have hprod := hres.mul htwo
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1:ℝ) < s := hs
  unfold kappaFac
  push_cast
  rw [cFac_eq_zeta s hs1]
  ring
