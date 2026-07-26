  have hcongr : (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹)
      = ∏' p : {p : ℕ // p.Prime}, (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    apply tprod_congr
    intro p
    rw [zOmegaHom_prime s z p.2]
  rw [hcongr]
  have hsplit := tprod_split_two
    (fun n : ℕ => (1 - z * (((n:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) hmul3
  rw [hsplit.2]
