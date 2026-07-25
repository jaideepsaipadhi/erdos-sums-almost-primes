/-- A1 step 4a: membership — naturals below N are N-smooth. -/
theorem mem_smoothNumbers_of_lt (N m : ℕ) (hm : 0 < m) (hlt : m < N) :
    m ∈ N.smoothNumbers := by
  rw [Nat.mem_smoothNumbers]
  refine ⟨ hm.ne', ?_⟩
  intro p hp hpm
  exact lt_of_le_of_lt (Nat.le_of_dvd hm hpm) hlt
