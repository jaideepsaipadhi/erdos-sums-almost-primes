/-- Terms with Omega(n) = k >= 1 automatically have n >= 2. -/
theorem two_le_of_bigOmega_eq (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (h : bigOmega n = k) : 2 ≤ n := by
  by_contra hcon
  push_neg at hcon
  interval_cases n
  · have : bigOmega 0 = 0 := by unfold bigOmega; simp
    omega
  · have : bigOmega 1 = 0 := by unfold bigOmega; simp
    omega
