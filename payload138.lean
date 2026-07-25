/-- If the p >= 5 tail is multipliable, so is the p >= 3 family, and the
product splits off the p = 3 factor. -/
theorem tprod_split_three {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    [ContinuousMul M] (f : ℕ → M)
    (hf5 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => f p)
      ∧ (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, f p)
        = f 3 * ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p := by
  sorry
