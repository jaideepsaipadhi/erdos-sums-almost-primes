/-- Probe: does Mathlib's Nat.Primes-indexed Euler product typecheck against
tprod_split_two's {p // p.Prime} spelling without a bridge? -/
theorem zeta_split_probe (s : ℝ) (hs : 1 < s) :
    (∏' p : {p : ℕ // p.Prime}, (1 - (((p:ℕ):ℝ) : ℂ) ^ (-(s:ℂ)))⁻¹)
      = riemannZeta (s : ℂ) := by
  have hre : (1:ℝ) < ((s : ℂ)).re := by simpa using hs
  have h := riemannZeta_eulerProduct_tprod hre
  rw [← h]
  apply tprod_congr
  intro p
  congr 1
  congr 1
  rw [Complex.ofReal_natCast]
