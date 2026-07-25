  have hsum_le : (∑ x ∈ u, Norm.norm (zOmegaHom s z x))
      ≤ ∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m) := by
    sorry
  have hval : (∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m))
      = ∏ p ∈ N.primesBelow, (1 - zOmegaNormHom s z p)⁻¹ := hgeo.2.tsum_eq
  have hfin : (∏ i ∈ Finset.range N, G i) ≤ ∏' i : ℕ, G i :=
    hGmult.prod_le_tprod _ (fun i _ => hGone i)
  calc (∑ x ∈ u, Norm.norm (zOmegaHom s z x))
      ≤ ∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m) := hsum_le
    _ = ∏ p ∈ N.primesBelow, (1 - zOmegaNormHom s z p)⁻¹ := hval
    _ = ∏ i ∈ Finset.range N, G i := hbridge
    _ ≤ ∏' i : ℕ, G i := hfin
