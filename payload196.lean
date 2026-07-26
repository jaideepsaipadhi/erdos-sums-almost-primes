/-- The manuscript's G2 at s = 1, section 3.2, defined explicitly:
G2(1,z) = 2^(-z) * prod_{p>2} (1 - z/p)^(-1) (1 - 1/p)^z.
NOT obtained as a limit of G2manu: cFac 1 diverges, so kappaFac 1 is a junk
value (0) and G2manu s z at s = 1 would collapse.  Anchors (checked
numerically): G2at1 1 = 1/2 (section 1), G2at1 2 = d (equation (1)). -/
noncomputable def G2at1 (z : ℂ) : ℂ :=
  (((1/2 : ℝ)) : ℂ) ^ z * G2C 1 z

/-- Manuscript section 3.2: c_i = [z^i] G2(1,z). -/
noncomputable def cCoeff (i : ℕ) : ℂ :=
  iteratedDeriv i G2at1 0 / (Nat.factorial i : ℂ)
