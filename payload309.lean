/-- Sm's integrand is integrable on (1,2].
Transfers from integrable_Jint_integrand through integrableOn_Ioc_subst.
Without this, Sm would be Lean's junk value for a non-integrable integral, and
Am, deltaM and Theorem 4.1 would all be vacuous. -/
theorem integrable_Sm_integrand (l j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (2:ℝ) ^ (-(j:ℝ) * s))
      (Set.Ioc (1:ℝ) 2) := by
  apply integrableOn_Ioc_subst
  have hJ := integrable_Jint_integrand (j:ℝ) (by positivity) l
  have hconst := hJ.const_mul (((Nat.factorial l : ℝ))⁻¹ * (2:ℝ) ^ (-(j:ℝ)))
  apply hconst.congr_fun _ measurableSet_Ioi
  intro u hu
  have hexp : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
  rw [show (-(j:ℝ)) * (1 + Real.exp (-u)) = -(j:ℝ) + -(j:ℝ) * Real.exp (-u) by ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  field_simp
  ring
