  have hcompl : HasProd (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := by
    have hbase : HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)
        (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := hf5.hasProd
    exact (compl_b3_equiv.hasProd_iff).mpr hbase
  have hequiv : Multipliable (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g)) :=
    hcompl.multipliable
