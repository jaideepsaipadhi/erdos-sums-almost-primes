/-- G2manu is differentiable in z on the closed disc of radius 12/5, for each
fixed s.  The s-independent half of Lemma 3.8; generalises
G2at1_differentiableOn_wide from s = 1. -/
theorem G2manu_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) :
    DifferentiableOn ℂ (fun z : ℂ => G2manu s z) (Metric.closedBall (0:ℂ) (12/5 : ℝ)) := by
  have hsub : Metric.closedBall (0:ℂ) (12/5 : ℝ) ⊆ Metric.ball (0:ℂ) (5/2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcpow : DifferentiableOn ℂ (fun z : ℂ => ((kappaFac s : ℝ) : ℂ) ^ z)
      (Metric.closedBall (0:ℂ) (12/5 : ℝ)) := by
    apply Differentiable.differentiableOn
    intro z
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hk
  have hG2C : DifferentiableOn ℂ (fun z : ℂ => G2C s z)
      (Metric.closedBall (0:ℂ) (12/5 : ℝ)) :=
    (G2C_differentiableOn_wide s hs).mono hsub
  unfold G2manu
  exact hcpow.mul hG2C
