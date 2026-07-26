/-- Manuscript normalisation bridge: kappa s = (s-1) * cFac s.
Then the manuscript's G2(s,z) = kappa(s)^z * G2C(s,z), and kappa(1) = 1/2,
recovering G2(1,z) = 2^(-z) * prod_{p>2} (...) of section 3.2. -/
noncomputable def kappaFac (s : ℝ) : ℝ := (s - 1) * cFac s

/-- kappa is positive on (1,2]. -/
theorem kappaFac_pos (s : ℝ) (hs : 1 < s) (hc : 0 < cFac s) : 0 < kappaFac s := by
  unfold kappaFac
  have h1 : (0:ℝ) < s - 1 := by linarith
  positivity

/-- The manuscript's G2, expressed through our G2C. -/
noncomputable def G2manu (s : ℝ) (z : ℂ) : ℂ :=
  ((kappaFac s : ℝ) : ℂ) ^ z * G2C s z
