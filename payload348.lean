/-- Lemma 3.9's bracket C(s,z) = z c(s,z), as a function of s and z.
Naming it lets the s -> 1 limit and the coefficient extraction be stated
without repeating the three-part expression. f is the log-derivative of
zetaTilde, carried as a parameter. -/
noncomputable def cBracket (fs : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  z * (((fs + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)
    + ((-(z * (z - 1) * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
        / ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
          / ((((((3:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z))
      + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
          (-(z * (z - 1) * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
            / ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
              / ((((((p:ℕ):ℝ)) ^ s : ℝ) : ℂ) - z)))

/-- Lemma 3.9 restated with the bracket named. -/
theorem lemma_3_9_bracket (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1:ℝ) 2) (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ => G2manu t z) (G2manu s z * cBracket (f s) s z) s := by
  unfold cBracket
  exact lemma_3_9_complex z hz s hsmem f hf
