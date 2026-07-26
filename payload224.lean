/-- The coercion carries real s -> 1+ into the complex right half-plane at 1. -/
theorem ofReal_tendsto_halfplane :
    Filter.Tendsto (fun s : ℝ => (s : ℂ))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhdsWithin 1 {z : ℂ | 1 < z.re}) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hcont : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhds 1) (nhds ((1:ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1)
    simpa using hcont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    exact hs
