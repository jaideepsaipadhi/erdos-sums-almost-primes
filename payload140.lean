  have hcompl : HasProd (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := by
    have hbase : HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)
        (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := hf5.hasProd
    have hiff := (primesGE3_ne_equiv.hasProd_iff
      (f := fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)
      (a := ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p))
    have htrans : HasProd
        ((fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)  ∘  primesGE3_ne_equiv)
        (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := hiff.mpr hbase
    apply htrans.congr_fun
    sorry
  have hequiv : Multipliable (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g)) :=
    hcompl.multipliable
