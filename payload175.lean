/-- C2: term-by-term differentiation, j times, on the ball of radius 3/2. -/
theorem iteratedDeriv_tsum_eq (s : ℝ) (hs : 1 < s) (r0 r : ℝ)
    (hr00 : 0 < r0) (hr0r : r0 < r) (hr0 : 0 ≤ r)
    (hr3 : r * ((3:ℝ) ^ (-s)) ≤ 1/2) (hr2 : r < (2:ℝ) ^ s) :
    ∀ j : ℕ, ∀ w : ℂ, Norm.norm w < r0 →
      iteratedDeriv j (fun z : ℂ => ∑' n : ℕ, zOmegaHom s z n) w
        = ∑' n : ℕ, iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w := by
  sorry
