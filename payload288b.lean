/-- d/ds G2manu exists at every point of (1,2) on the contour: this is what
makes `deriv (fun u => G2manu u w) x` in Lemma 3.8 denote a real derivative
rather than a junk value. -/
theorem G2manu_differentiableAt_s (w : ℂ) (hw : Norm.norm w ≤ 2) (x : ℝ)
    (hx : x ∈ Set.Ioo (1:ℝ) 2) (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x) :
    DifferentiableAt ℝ (fun u : ℝ => G2manu u w) x :=
  (lemma_3_9_complex w hw x hx f hf).differentiableAt
