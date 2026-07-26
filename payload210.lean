/-- Manuscript (4): the S1 source, D_k = I_k - I'_k.
Ikfrozen is C-valued (built from cCoeff), so take the real part. -/
noncomputable def Dk (k : ℕ) : ℝ := Ik k - (Ikfrozen k).re

/-- Manuscript section 2.3: E1(k) = 2^k D_k. -/
noncomputable def E1k (k : ℕ) : ℝ := (2:ℝ) ^ k * Dk k

/-- Manuscript section 2.3: the exponentially small source
Eexp(k) = 2^(k+1) w_k - q k^2 W_k - 2^k T_k, with q = log 2 / 4. -/
noncomputable def Eexpk (k : ℕ) : ℝ :=
  (2:ℝ) ^ (k + 1) * wk k - (Real.log 2 / 4) * (k : ℝ) ^ 2 * Wk k - (2:ℝ) ^ k * Tk k
