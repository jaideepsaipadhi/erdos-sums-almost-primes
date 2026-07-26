/-- The regularised zeta factor: (s-1) * zeta(s), extended by 1 at s = 1.
Smooth on [1, infinity) by GLW Lemma 11 / the standard pole structure; here we
only need the value at 1, which holds definitionally.  Real-valued because
zeta is real on the real axis for s > 1. -/
noncomputable def zetaTilde (s : ℝ) : ℝ :=
  if s = 1 then 1 else (s - 1) * (riemannZeta (s : ℂ)).re

/-- The extension is by the residue: zetaTilde 1 = 1 definitionally. -/
theorem zetaTilde_one : zetaTilde 1 = 1 := by
  unfold zetaTilde
  simp
