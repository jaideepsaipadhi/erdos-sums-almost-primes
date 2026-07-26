/-- Taylor bridge without a global analyticity hypothesis: over a complete
space, HasFPowerSeriesOnBall alone determines the iterated derivatives.
Weakening of iteratedDeriv_eq_factorial_smul_coeff, which required
AnalyticOn C f univ and so could not be applied to functions with poles
(e.g. G2C, whose nearest pole is at z = 3). -/
theorem iteratedDeriv_eq_factorial_smul_coeff'
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : EℕReal}
    (h : HasFPowerSeriesOnBall f p 0 r) (n : ℕ) :
    iteratedDeriv n f 0 = (Nat.factorial n : ℂ) * p.coeff n := by
  have hv := h.iteratedFDeriv_eq_sum_of_completeSpace (v := fun _ : Fin n => (1:ℂ))
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hv]
  have hconst : ∀ σ : Equiv.Perm (Fin n),
      p n (fun i => (fun _ : Fin n => (1:ℂ)) (σ i)) = p.coeff n := by
    intro σ
    rfl
  rw [Finset.sum_congr rfl (fun σ _ => hconst σ)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [nsmul_eq_mul]
