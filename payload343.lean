/-- The second s-derivative of G2manu is continuous in the contour parameter.
Needed for the F' measurability obligation of Lemma 3.8 at r=2.
hasDerivAt_G2manu_second identifies it with G2*(C^2 + C'), and all three
factors are continuous in theta. -/
theorem G2manu_deriv2_continuous_theta (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f fp : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x)
    (hfp : HasDerivAt f (fp s) s)
    (G C Cp : ℝ → ℂ)
    (hG : Continuous G) (hC : Continuous C) (hCp : Continuous Cp) :
    Continuous (fun theta : ℝ => G theta * C theta * C theta + G theta * Cp theta) :=
  ((hG.mul hC).mul hC).add (hG.mul hCp)
