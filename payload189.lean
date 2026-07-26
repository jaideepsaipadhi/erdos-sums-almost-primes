  obtain ⟨ r, hrgt, hr3, hr2 ⟩ := exists_radius_gap s hs
  have hC2 := iteratedDeriv_tsum_eq s hs (3/2) r (by norm_num) hrgt
    (by linarith) hr3 hr2 k 0 (by norm_num)
  rw [hC2]
  have hcollapse : (∑' n : ℕ, iteratedDeriv k (fun z : ℂ => zOmegaHom s z n) 0)
      = ∑' n : ℕ,
        (if bigOmega n = k then (Nat.factorial k : ℂ) * (((n:ℂ)) ^ (-(s:ℂ))) else 0) := by
    apply tsum_congr
    intro n
    exact iteratedDeriv_term_at_zero s k hk n
  rw [hcollapse]
  sorry
