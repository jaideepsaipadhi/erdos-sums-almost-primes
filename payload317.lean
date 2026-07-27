/-- Integrability of the (s-1)-weighted integrand on (1,2].
Under s = 1 + e^(-u) it becomes u^l/l! * e^(-2u), integrable on (0,inf).
This is the dominating integrand for bound (10). -/
theorem integrable_log_pow_sub_one (l : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1))
      (Set.Ioc (1:ℝ) 2) := by
  apply integrableOn_Ioc_subst
  have hbase : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ l * Real.exp (-(2 * u))) (Set.Ioi (0:ℝ)) :=
    integrable_pow_exp_two l
  have hconst := hbase.const_mul (((Nat.factorial l : ℝ))⁻¹)
  apply MeasureTheory.IntegrableOn.congr_fun hconst _ measurableSet_Ioi
  intro u hu
  simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
  rw [show Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) by
    rw [← Real.exp_add]; ring_nf]
  field_simp
  ring
