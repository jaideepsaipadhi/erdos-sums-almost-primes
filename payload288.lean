/-- MANUSCRIPT LEMMA 3.8 (r = 1): g_i is differentiable in s on (1,2), with
  d/ds g_i(s) = [z^i] (d/ds G2)(s, .),
the derivative taken under the contour |z| = 12/5.

Hypotheses:
  f, hf  -- the log-derivative of zetaTilde on the whole interval (not just at
            a point): the differentiation-under-the-integral lemma needs the
            pointwise derivative for every x in a neighbourhood.
  M, hM  -- sup_{t in (1,2), |w| = 12/5} ||d_s G2manu t w||, the analogue of
            the manuscript's M1 but at radius 12/5 (2.9 exceeds the proven
            analyticity radius 5/2).  Certified numerically in section 3.5,
            so a hypothesis here, as with d_enclosure.

Only r = 1 and r = 2 are ever consumed (section 3.5 and Theorem 6.1); the
manuscript's C^infinity is never used. -/
theorem lemma_3_8_r1 (i : ℕ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Ioo (1:ℝ) 2, ∀ theta : ℝ,
      Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) x) ≤ M) :
    HasDerivAt (fun t : ℝ => gManu i t)
      ((2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (∫ theta in (0:ℝ)..(2 * Real.pi),
          deriv (circleMap 0 (12/5 : ℝ)) theta
            * ((1 / circleMap 0 (12/5 : ℝ) theta) ^ i
              * ((circleMap 0 (12/5 : ℝ) theta)⁻¹
                * deriv (fun u : ℝ => G2manu u (circleMap 0 (12/5 : ℝ) theta)) s)))) s := by
  sorry
