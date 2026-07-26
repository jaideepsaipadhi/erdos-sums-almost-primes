/-- Wide-radius variant: G2at1 differentiable on closedBall 0 (12/5).
Radius 12/5 sits inside ball 0 (5/2) and strictly contains z = 2, which is
what sum 2^i c_i = d needs. -/
theorem G2at1_differentiableOn_wide :
    DifferentiableOn ℂ G2at1 (Metric.closedBall (0:ℂ) (12/5 : ℝ)) := by
  have hsub : Metric.closedBall (0:ℂ) (12/5 : ℝ) ⊆ Metric.ball (0:ℂ) (5/2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcpow : DifferentiableOn ℂ (fun z : ℂ => (((1/2 : ℝ)) : ℂ) ^ z)
      (Metric.closedBall (0:ℂ) (12/5 : ℝ)) := by
    apply Differentiable.differentiableOn
    intro z
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    simp only [ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hG2C : DifferentiableOn ℂ (fun z : ℂ => G2C 1 z)
      (Metric.closedBall (0:ℂ) (12/5 : ℝ)) :=
    (G2C_differentiableOn_wide 1 (le_refl 1)).mono hsub
  unfold G2at1
  exact hcpow.mul hG2C
