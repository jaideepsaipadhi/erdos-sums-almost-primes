    have hmain := hasSum_deriv_of_summable_norm hbound hdiff hball hle hwmem
    have hIHball : (fun v : ℂ => iteratedDeriv J (fun z : ℂ => ∑' n : ℕ, zOmegaHom s z n) v)
        =ᶠ[nhds w] fun v : ℂ => ∑' n : ℕ, iteratedDeriv J (fun z : ℂ => zOmegaHom s z n) v := by
      filter_upwards [hball.mem_nhds hwmem] with v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      exact IH v hv
    rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hIHball, ← hmain.tsum_eq]
    apply tsum_congr
    intro n
    rw [iteratedDeriv_succ]
