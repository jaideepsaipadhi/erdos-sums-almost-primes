/-- The two-argument limit: cBracket (f s) s z -> cBracket f1 1 z as s -> 1+.
Splits via cBracket_sub_first into f's convergence and the fixed-fs limit. -/
theorem cBracket_tendsto_two_arg (z : ℂ) (hz : Norm.norm z ≤ 2)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds f1)) :
    Filter.Tendsto (fun s : ℝ => cBracket (f s) s z)
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (cBracket f1 1 z)) := by
  have hfix := cBracket_tendsto_at_one f1 z hz
  have hdiff : Filter.Tendsto (fun s : ℝ => z * (((f s - f1 : ℝ)) : ℂ))
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds 0) := by
    have hz0 : Filter.Tendsto (fun s : ℝ => ((f s - f1 : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds 0) := by
      have := (hfc.sub tendsto_const_nhds)
      simp only [sub_self] at this
      exact (Complex.continuous_ofReal.continuousAt).tendsto.comp this
    have := hz0.const_mul z
    simpa using this
  have hsum := hdiff.add hfix
  simp only [zero_add] at hsum
  apply hsum.congr
  intro s
  have := cBracket_sub_first (f s) f1 s z
  linear_combination (norm := ring_nf) this
