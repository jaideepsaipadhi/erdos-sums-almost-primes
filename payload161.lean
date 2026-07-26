/-- Splitting a product over all primes into p = 2 and the p >= 3 tail. -/
theorem tprod_split_two {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    [ContinuousMul M] (f : ℕ → M)
    (hf3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => f p)) :
    Multipliable (fun p : {p : ℕ // p.Prime} => f p)
      ∧ (∏' p : {p : ℕ // p.Prime}, f p)
        = f 2 * ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, f p := by
  classical
  set b2 : {p : ℕ // p.Prime} := ⟨ 2, Nat.prime_two ⟩ with hb2
  set g : {p : ℕ // p.Prime} → M := fun p => f p with hg
  have hsingle : HasProd ((({b2} : Set {p : ℕ // p.Prime}).restrict g)) (g b2) :=
    hasProd_singleton b2 g
  have hcompl : HasProd (((({b2} : Set {p : ℕ // p.Prime})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, f p) :=
    (compl_two_equiv.hasProd_iff).mpr hf3.hasProd
  have hall := hsingle.mul_compl hcompl
  exact ⟨ hall.multipliable, hall.tprod_eq ⟩
