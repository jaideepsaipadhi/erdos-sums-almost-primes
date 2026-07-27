/-- The real derivative of t |-> p^(-t), extracted so both the real and the
complex chains can use it. -/
theorem hasDerivAt_rpow_neg (p : ℕ) (hp : 3 ≤ p) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ((p:ℝ)) ^ (-t))
      (-(((p:ℝ)) ^ (-s) * Real.log (p:ℝ))) s := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hrw : (fun t : ℝ => ((p:ℝ)) ^ (-t))
      = fun t : ℝ => Real.exp ((-t) * Real.log (p:ℝ)) := by
    funext t
    rw [Real.rpow_def_of_pos hp0, mul_comm]
  rw [hrw]
  have hinner : HasDerivAt (fun t : ℝ => (-t) * Real.log (p:ℝ))
      (-Real.log (p:ℝ)) s := by
    simpa using (hasDerivAt_neg s).mul_const (Real.log (p:ℝ))
  have h := hinner.exp
  convert h using 1
  rw [show Real.exp (-s * Real.log (p:ℝ)) = ((p:ℝ)) ^ (-s) by
    rw [Real.rpow_def_of_pos hp0, mul_comm]]
  ring
