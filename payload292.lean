/-- The s-derivative of G2manu, as a function of the contour parameter theta,
is continuous.  This is what makes the F' measurability obligation of
Lemma 3.8 discharge: lemma_3_9_complex identifies the deriv with an explicit
expression, and every factor of that expression is continuous in theta. -/
theorem G2manu_deriv_continuous_theta (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x) :
    Continuous (fun theta : ℝ =>
      deriv (fun u : ℝ => G2manu u (circleMap 0 (2:ℝ) theta)) s) := by
  have hs1 : 1 ≤ s := le_of_lt hsmem.1
  have hkap : 0 < kappaFac s := kappaFac_pos s hsmem.1 (cFac_pos s hsmem.1)
  have hcm : Continuous (circleMap 0 (2:ℝ)) := continuous_circleMap 0 _
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2:ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  have hval : ∀ theta : ℝ,
      deriv (fun u : ℝ => G2manu u (circleMap 0 (2:ℝ) theta)) s
        = G2manu s (circleMap 0 (2:ℝ) theta) *
          (circleMap 0 (2:ℝ) theta * (((f s + Real.log 2 / ((2:ℝ) ^ s - 1) : ℝ)) : ℂ)
            + ((-(circleMap 0 (2:ℝ) theta * (circleMap 0 (2:ℝ) theta - 1)
                  * ((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ))
                / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((3:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2:ℝ) theta))
              + ∑' p : {p : ℕ // p.Prime AND 5 ≤ p},
                  (-(circleMap 0 (2:ℝ) theta * (circleMap 0 (2:ℝ) theta - 1)
                      * ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ))
                    / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                      / (((((((p:ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2:ℝ) theta)))) := by
    intro theta
    exact (lemma_3_9_complex (circleMap 0 (2:ℝ) theta) (hnorm theta) s hsmem f
      (hf s hsmem)).deriv
  simp only [hval]
  have hG2 : Continuous (fun theta : ℝ => G2manu s (circleMap 0 (2:ℝ) theta)) := by
    have hsub : Metric.closedBall (0:ℂ) (2:ℝ) ⊆ Metric.closedBall (0:ℂ) ((12:ℝ)/5) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      linarith
    have hmem : ∀ theta : ℝ, circleMap 0 (2:ℝ) theta IN
        Metric.closedBall (0:ℂ) (2:ℝ) := by
      intro theta
      rw [Metric.mem_closedBall, dist_zero_right]
      simp [circleMap]
    exact (((G2manu_differentiableOn_wide s hs1 hkap).mono hsub).continuousOn).comp_continuous
      hcm hmem
  apply hG2.mul
  apply Continuous.add
  · exact hcm.mul continuous_const
  · exact (clog_term_continuous_theta 3 (le_refl 3) s hs1).add
      (clog_series_continuous_theta s hs1)
