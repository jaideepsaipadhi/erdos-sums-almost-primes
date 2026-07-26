/-- D2: the regularised family at z = 2, s = 1 is multipliable.
Immediate from reg_multipliable_three, since ||(2:C)|| = 2 <= 2. -/
theorem reg_multipliable_three_at_two :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - (2:ℂ) * ((((p:ℕ):ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ))⁻¹
        * (((1 - ((p:ℕ):ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ)) ^ (2:ℂ)) := by
  have h := reg_multipliable_three 1 (le_refl 1) 2 (by norm_num)
  exact h
