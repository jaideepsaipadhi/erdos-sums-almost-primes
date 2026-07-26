/-- Manuscript section 3.4: S* = sum_{i>=0} 2^i |c_i|, the unsigned bound
constant for the convolution Delta(k).  Certified S* <= 6.9763.
Previously a bare literal, which left Sstar_bound vacuous. -/
noncomputable def SstarConst : ℝ :=
  ∑' i : ℕ, (2:ℝ) ^ i * Norm.norm (cCoeff i)

/-- Manuscript section 3.5: alpha_+ is the constant in B_1(k) <= alpha_+ (k+1).
STILL A LITERAL: the real definition needs the beta_i interval sweep of
section 3.5, which is not yet formalised.  alpha_bound is vacuous until then. -/
noncomputable def alphaConst : ℝ := 15.5716

/-- Manuscript Theorem 6.1: Gamma = (1/2) sum_{i>=1} gammahat_i 2^i, the
k-independent remainder bound.  STILL A LITERAL: needs gammahat_i, i.e. the
second s-derivative G2^(2,0) and its interval sweep.  Gamma_bound is vacuous
until then. -/
noncomputable def GammaConst : ℝ := 105.41
