/-- The single derivative computation behind Lemma 3.9's per-prime term:
d/ds log(1 - c*p^(-s)) = c*log p*p^(-s)/(1 - c*p^(-s)).
Applied at c = z and c = 1 to get the two halves of the log-factor.
Verified numerically at (p,s,c) = (3,1.4,1.3),(5,1.7,0.9),(11,1.2,1),(3,1,2). -/
theorem deriv_log_one_sub_const_rpow (p : ℕ) (hp : 3 ≤ p) (c s : ℝ)
    (hne : (1:ℝ) - c * ((p:ℝ)) ^ (-s) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (1 - c * ((p:ℝ)) ^ (-t)))
      (c * Real.log (p:ℝ) * ((p:ℝ)) ^ (-s) / (1 - c * ((p:ℝ)) ^ (-s))) s := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hbase : HasDerivAt (fun t : ℝ => ((p:ℝ)) ^ (-t))
      (-(((p:ℝ)) ^ (-s) * Real.log (p:ℝ))) s := by
    have hrw : (fun t : ℝ => ((p:ℝ)) ^ (-t))
        = fun t : ℝ => Real.exp ((-t) * Real.log (p:ℝ)) := by
      funext t
      rw [Real.rpow_def_of_pos hp0]
      ring_nf
    rw [hrw]
    have hinner : HasDerivAt (fun t : ℝ => (-t) * Real.log (p:ℝ))
        (-Real.log (p:ℝ)) s := by
      simpa using (hasDerivAt_neg s).mul_const (Real.log (p:ℝ))
    have h := hinner.exp
    convert h using 1
    rw [show Real.exp (-s * Real.log (p:ℝ)) = ((p:ℝ)) ^ (-s) by
      rw [Real.rpow_def_of_pos hp0]; ring_nf]
    ring
  have hin : HasDerivAt (fun t : ℝ => 1 - c * ((p:ℝ)) ^ (-t))
      (c * (((p:ℝ)) ^ (-s) * Real.log (p:ℝ))) s := by
    have h := (hbase.const_mul c).const_sub 1
    convert h using 1
    ring
  have h := (Real.hasDerivAt_log hne).comp s hin
  simp only [Function.comp_def] at h
  convert h using 1
  field_simp
