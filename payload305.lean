/-- Interior form of the mean value bound: for 1 < t, s < 2,
||g_i(s) - g_i(t)|| <= beta * |s - t|, given a derivative bound beta on (1,2).
The endpoint version follows by letting t -> 1+ and using gManu_tendsto_cCoeff. -/
theorem gManu_lipschitz_interior (i : ℕ) (beta : ℝ)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (t s : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 2) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    Norm.norm (gManu i s - gManu i t) ≤ beta * Norm.norm (s - t) := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun x : ℝ => deriv (fun u : ℝ => gManu i u) x)
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_Ioo 1 2) ht hs
