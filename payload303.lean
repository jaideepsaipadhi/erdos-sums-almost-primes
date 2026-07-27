/-- cCoeff as a contour integral at radius 2, the G2at1 analogue of
gManu_eq_circleIntegral.  G2at1 is differentiable on closedBall 0 (12/5)
(G2at1_differentiableOn_wide), which contains closedBall 0 2. -/
theorem cCoeff_eq_circleIntegral (i : ℕ) :
    cCoeff i
      = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (circleIntegral (fun z : ℂ => (1 / z) ^ i • z⁻¹ • G2at1 z)
          0 (2 : ℝ)) := by
  have hdiff : DifferentiableOn ℂ G2at1 (Metric.closedBall (0:ℂ) ((2 : NNReal) : ℝ)) := by
    apply G2at1_differentiableOn_wide.mono
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    norm_num at hw ⊢
    linarith
  have hR : (0:NNReal) < 2 := by norm_num
  have hser := hdiff.hasFPowerSeriesOnBall hR
  have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser i
  have hcoeff : cCoeff i
      = (cauchyPowerSeries G2at1 0 ((2 : NNReal) : ℝ)).coeff i := by
    unfold cCoeff
    rw [hbridge]
    have hfac : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    field_simp
  rw [hcoeff]
  have h := cauchyPowerSeries_apply G2at1 0 ((2 : NNReal) : ℝ) i 1
  show ((cauchyPowerSeries G2at1 0 ((2 : NNReal) : ℝ) i) fun _ => 1) = _
  rw [h]
  norm_num
