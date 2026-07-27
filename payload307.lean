/-- MANUSCRIPT section 3.5: the exact evaluation
  int_1^2 (-log(s-1))^l / l! * (s-1) ds = 2^(-l-1).
Substitution s = 1 + e^(-t) (integral_Ioc_subst) turns it into
int_0^inf u^l/l! * e^(-2u) du, evaluated by integral_pow_exp_neg_two_mul.
Verified numerically at l = 0,1,2,5. -/
theorem integral_log_pow_sub_one (l : ℕ) :
    (∫ s in Set.Ioc (1:ℝ) 2,
      (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1))
      = 1 / (2:ℝ) ^ (l + 1) := by
  rw [integral_Ioc_subst (fun s : ℝ =>
    (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1))]
  have hsimp : ∀ u : ℝ, u ∈ Set.Ioi (0:ℝ) →
      Real.exp (-u) * ((-Real.log ((1 + Real.exp (-u)) - 1)) ^ l / (Nat.factorial l)
          * ((1 + Real.exp (-u)) - 1))
        = u ^ l / (Nat.factorial l) * Real.exp (-2 * u) := by
    intro u _
    simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
    rw [show Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) by
      rw [← Real.exp_add]; ring_nf]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsimp]
  have hfactor : ∀ u : ℝ, u ^ l / (Nat.factorial l) * Real.exp (-2 * u)
      = ((Nat.factorial l : ℝ))⁻¹ * (u ^ l * Real.exp (-2 * u)) := by
    intro u
    field_simp
    ring
  simp only [hfactor]
  rw [MeasureTheory.integral_const_mul, integral_pow_exp_neg_two_mul]
  have hfac : ((Nat.factorial l : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  field_simp
