/-- MANUSCRIPT LEMMA 3.8 (r = 1): differentiation under the contour.
d/ds of the contour integral equals the contour integral of d/ds.

f, hf : the log-derivative of zetaTilde on the whole interval -- the
  differentiation lemma needs the derivative at every point of a neighbourhood.
M, hM : sup over the contour of ||d_s G2manu||, the analogue of the
  manuscript's M1 at radius 2 (the proven analyticity radius is 5/2, and
  lemma_3_9_complex holds for ||z|| <= 2, so the contour sits at 2). -/
theorem lemma_3_8_integral_r1 (i : ℕ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Ioo (1:ℝ) 2, ∀ theta : ℝ,
      Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2:ℝ) theta)) x) ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ theta in (0:ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2manu t (circleMap 0 (2:ℝ) theta))))
      (∫ theta in (0:ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹
              * deriv (fun u : ℝ => G2manu u (circleMap 0 (2:ℝ) theta)) s))) s := by
  sorry
