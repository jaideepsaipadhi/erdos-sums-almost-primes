  set N := u.sup id + 1 with hN
  have hsmooth : ∀ x ∈ u, x ≠ 0 → x ∈ N.smoothNumbers := by
    intro x hxu hx0
    apply mem_smoothNumbers_of_lt N x (Nat.pos_of_ne_zero hx0)
    have : x ≤ u.sup id := Finset.le_sup (f := id) hxu
    omega
  have hgeo := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := (zOmegaNormHom s z).toMonoidHom)
    (fun {p} hp => zOmegaNorm_prime_lt_one s hs z hz hp) N
  have hbridge : (∏ p ∈ N.primesBelow, (1 - zOmegaNormHom s z p)⁻¹)
      = ∏ i ∈ Finset.range N, G i := by
    rw [hG]
    rw [Finset.prod_mulIndicator_eq_prod_filter (Finset.range N)
      (fun _ p => (1 - Norm.norm z * ((p:ℝ) ^ (-s)))⁻¹)
      (fun _ => {p : ℕ | p.Prime}) id]
    rfl
  sorry
