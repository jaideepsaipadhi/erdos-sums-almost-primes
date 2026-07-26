/-- G2at1 is differentiable on the closed disc of radius 3/2.
The cpow factor (1/2)^z is entire; G2C 1 . is differentiable on ball 0 2,
which contains closedBall 0 (3/2).  Radius 3/2 is enough to reach z = 1
(giving sum c_i = 1/2); reaching z = 2 would need the radius pushed past 2. -/
theorem G2at1_differentiableOn :
    DifferentiableOn ℂ G2at1 (Metric.closedBall (0:ℂ) (3/2 : ℝ)) := by
  have hsub : Metric.closedBall (0:ℂ) (3/2 : ℝ) ⊆ Metric.ball (0:ℂ) 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcpow : DifferentiableOn ℂ (fun z : ℂ => (((1/2 : ℝ)) : ℂ) ^ z)
      (Metric.closedBall (0:ℂ) (3/2 : ℝ)) := by
    apply Differentiable.differentiableOn
    intro z
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    simp only [ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hG2C : DifferentiableOn ℂ (fun z : ℂ => G2C 1 z)
      (Metric.closedBall (0:ℂ) (3/2 : ℝ)) :=
    (G2C_differentiableOn 1 (le_refl 1)).mono hsub
  unfold G2at1
  exact hcpow.mul hG2C
