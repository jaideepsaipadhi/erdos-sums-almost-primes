theorem zOmega_summable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : ‖z‖ < (2:ℝ) ^ s) :
    Summable (fun n : ℕ => ‖zOmegaHom s z n‖) := by
  classical
  set G : ℕ → ℝ := Set.mulIndicator {p : ℕ | p.Prime}
    (fun p : ℕ => (1 - ‖z‖ * ((p:ℝ) ^ (-s)))⁻¹) with hG
  have hGmult : Multipliable G := zOmegaNorm_indicator_multipliable s hs z hz
  have hGone : ∀ i : ℕ, (1:ℝ) ≤ G i := by
    intro i
    rw [hG]
    by_cases hp : i ∈ {p : ℕ | p.Prime}
    · rw [Set.mulIndicator_of_mem hp]
      exact zOmega_factor_ge_one s hs z hz i hp
    · rw [Set.mulIndicator_of_notMem hp]
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ ‖zOmegaHom s z n‖ := fun n => norm_nonneg _
  apply summable_of_sum_le hnn
  intro u
  sorry
