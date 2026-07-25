  classical
  set b3 : {p : ℕ // p.Prime ∧ 3 ≤ p} := ⟨ 3, Nat.prime_three, le_refl 3 ⟩ with hb3
  set g : {p : ℕ // p.Prime ∧ 3 ≤ p} → M := fun p => f p with hg
  have hsingle : HasProd ((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p}).restrict g)) (g b3) := by
    have := hasProd_singleton b3 g
    exact this
  have hequiv : Multipliable (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g)) := by
    sorry
  have hcompl : HasProd (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := by
    sorry
  have hall := hsingle.mul_compl hcompl
  refine ⟨ hall.multipliable, ?_⟩
  rw [hall.tprod_eq]
