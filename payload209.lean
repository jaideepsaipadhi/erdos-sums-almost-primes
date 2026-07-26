/-- Manuscript section 2.3 partial sums and tails.
U_k = sum_{i<=k} i 2^i c_i,  V_k = sum_{i<=k} i^2 2^i c_i,
W_k = sum_{i>k} 2^i c_i,     w_k = sum_{i>k} c_i,
Delta(k) = sum_{i<=k} 2^i c_i delta_{k-i}. -/
noncomputable def Uk (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (i : ℝ) * 2 ^ i * (cCoeff i).re

noncomputable def Vk (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (i : ℝ) ^ 2 * 2 ^ i * (cCoeff i).re

noncomputable def Wk (k : ℕ) : ℝ :=
  ∑' i : ℕ, (if k < i then (2:ℝ) ^ i * (cCoeff i).re else 0)

noncomputable def wk (k : ℕ) : ℝ :=
  ∑' i : ℕ, (if k < i then (cCoeff i).re else 0)

/-- The signed convolution of section 3.4. -/
noncomputable def DeltaConv (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (2:ℝ) ^ i * (cCoeff i).re * deltaM (k - i)

/-- E(k) defined by f_k = 1 - 2^(-k)(a1 k^2 + E(k)), i.e. solved for E(k). -/
noncomputable def Ek (k : ℕ) : ℝ :=
  (2:ℝ) ^ k * (1 - f k) - aOneConst * (k : ℝ) ^ 2
