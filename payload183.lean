  intro j
  induction j with
  | zero =>
    intro w hw
    simp only [iteratedDeriv_zero]
  | succ J IH =>
    intro w hw
    have hball : IsOpen (Metric.ball (0:ℂ) r0) := Metric.isOpen_ball
    have hwmem : w ∈ Metric.ball (0:ℂ) r0 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw
    have hbound := deriv_bound_summable s hs J r0 r hr01 hr0r hr0 hr3 hr2
    have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
        (fun v : ℂ => iteratedDeriv J (fun z : ℂ => zOmegaHom s z n) v)
        (Metric.ball (0:ℂ) r0) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        have hzero : (fun v : ℂ => iteratedDeriv J (fun z : ℂ => zOmegaHom s z 0) v)
            = fun _ : ℂ => (0:ℂ) := by
          funext v
          exact iteratedDeriv_term_zero s J v
        rw [hzero]
        exact differentiableOn_const 0
      · exact (iteratedDeriv_term_differentiable s n hn J).differentiableOn
    have hle : ∀ (n : ℕ) (v : ℂ), v ∈ Metric.ball (0:ℂ) r0 TO
        Norm.norm (iteratedDeriv J (fun z : ℂ => zOmegaHom s z n) v)
          ≤ ((bigOmega n : ℕ) : ℝ) ^ J * r0 ^ (bigOmega n - J) * ((n:ℝ) ^ (-s)) := by
      intro n v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      by_cases hn : n = 0
      · subst hn
        rw [iteratedDeriv_term_zero s J v, norm_zero]
        positivity
      · exact iteratedDeriv_term_bound s hs r0 (by linarith) J n hn v (le_of_lt hv)
    sorry
