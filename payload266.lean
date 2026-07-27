/-- kappa(s) = zetaTilde(s) * (1 - 2^(-s)) for s > 1.
Real-part projection of cFac_eq_zeta.  This is what lets Lemma 3.9's kappa-part
split into f(s) + log 2/(2^s - 1), with f = (log zetaTilde)' carried opaquely
(the manuscript certifies f numerically via Stieltjes constants). -/
theorem kappaFac_eq_zetaTilde (s : ℝ) (hs : 1 < s) :
    kappaFac s = zetaTilde s * (1 - (2:ℝ) ^ (-s)) := by
  have hne : s ≠ 1 := ne_of_gt hs
  have hcast : ((1 : ℂ) - ((2:ℂ)) ^ (-(s:ℂ))) = (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) := by
    push_cast
    rw [show ((2:ℂ)) = (((2:ℝ)) : ℂ) by norm_num]
    rw [show (-(s:ℂ)) = (((-s : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    ring
  have hz := cFac_eq_zeta s hs
  rw [hcast] at hz
  have hre : cFac s = (riemannZeta (s:ℂ)).re * (1 - (2:ℝ) ^ (-s)) := by
    have := congrArg Complex.re hz
    simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using this
  unfold kappaFac zetaTilde
  rw [if_neg hne, hre]
  ring
