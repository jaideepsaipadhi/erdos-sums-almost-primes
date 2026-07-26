/-- C1 (radius form): if r0 < r and both satisfy the summability conditions,
the polynomially-weighted family at r0 is summable, because the polynomial
factor is absorbed by the ratio (r/r0)^Omega(n). -/
theorem omega_pow_summable_radius (s : ℝ) (hs : 1 < s) (j : ℕ)
    (r0 r : ℝ) (hr00 : 0 < r0) (hr0r : r0 < r)
    (hr0 : 0 ≤ r) (hr3 : r * ((3:ℝ) ^ (-s)) ≤ 1/2) (hr2 : r < (2:ℝ) ^ s) :
    Summable (fun n : ℕ =>
      ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n) * ((n:ℝ) ^ (-s))) := by
  sorry
