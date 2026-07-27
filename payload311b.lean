/-- gManu i is continuous on (1,2), from differentiability there. -/
theorem gManu_continuousOn (i : ℕ)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x) :
    ContinuousOn (fun t : ℝ => gManu i t) (Set.Ioo (1:ℝ) 2) :=
  fun x hx => ((hderiv x hx).continuousAt).continuousWithinAt
