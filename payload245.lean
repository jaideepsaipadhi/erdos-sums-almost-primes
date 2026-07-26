/-- MANUSCRIPT PROPOSITION 2.5 (exact decomposition).
E(k) = -q(2k U_k - V_k) - Delta(k) - E_1(k) + E_exp(k), with q = log 2 / 4.
Every term is a deterministic quantity; no error estimates enter here. -/
theorem prop_2_5 (k : ℕ) (hk : 1 ≤ k) :
    Ek k = -(Real.log 2 / 4) * (2 * (k : ℝ) * Uk k - Vk k)
             - DeltaConv k - E1k k + Eexpk k := by
  sorry
