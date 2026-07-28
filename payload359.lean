/-- The s-derivative of G2manu converges pointwise on the contour as s -> 1+:
G2manu s z * cBracket (f s) s z -> G2at1 z * cBracket f1 1 z = G2deriv1 f1 z.
The f-argument converges because f is continuous at 1 (hypothesis hfc). -/
theorem G2deriv_tendsto_at_one (z : ℂ) (hz : Norm.norm z ≤ 2)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds f1))
    (hbr : Filter.Tendsto (fun s : ℝ => cBracket (f s) s z)
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (cBracket f1 1 z))) :
    Filter.Tendsto (fun s : ℝ => G2manu s z * cBracket (f s) s z)
      (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (G2deriv1 f1 z)) := by
  unfold G2deriv1
  exact (G2manu_tendsto_G2at1 z hz).mul hbr
