/-- Lemma 3.8's contour representation, unfolded to an explicit circle integral.
Combines gManu_eq_cauchy_coeff with cauchyPowerSeries_apply at w = 1, c = 0.
The s-dependence sits entirely in G2manu s z; the (1/z)^i * z^(-1) factor is
s-free, which is what makes differentiation under the integral clean. -/
theorem gManu_eq_circleIntegral (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (i : ℕ) :
    gManu i s
      = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (circleIntegral (fun z : ℂ => (1 / z) ^ i • z⁻¹ • G2manu s z)
          0 (12/5 : ℝ)) := by
  rw [gManu_eq_cauchy_coeff s hs hk i]
  have h := cauchyPowerSeries_apply (fun z : ℂ => G2manu s z) 0 ((12/5 : NNReal) : ℝ) i 1
  unfold FormalMultilinearSeries.coeff
  rw [h]
  norm_num
