/-- MANUSCRIPT section 6.1's input: G2^(2,0) = G2 * (C^2 + C'), where C = z c.
This is the manuscript's G2(z^2 c^2 + z c') -- "a formula derived, not read:
differentiate d_s G2 = z c G2 once more".
Both f and its derivative fp are hypotheses, as in Lemma 3.9. -/
theorem hasDerivAt_G2manu_second (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) (f fp : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x)
    (hfp : HasDerivAt f (fp s) s)
    (C : ℝ → ℂ) (Cp : ℂ)
    (hC : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => G2manu t z) (G2manu x z * C x) x)
    (hCp : HasDerivAt C Cp s) :
    HasDerivAt (fun t : ℝ => G2manu t z * C t)
      (G2manu s z * C s * C s + G2manu s z * Cp) s := by
  have hG2 := hC s hsmem
  exact hG2.mul hCp
