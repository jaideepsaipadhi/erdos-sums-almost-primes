theorem sigma_reindex (k : ℕ) (F : ℕ → ℕ → ℂ) (G : ℕ → ℕ → ℂ)
    (hval : ∀ n i : ℕ, i ≤ n → n ≤ k → F n i = G (n - i) (k - n)) :
    ∑ x ∈ (Finset.range (k + 1)).sigma (fun n => Finset.range (n + 1)), F x.1 x.2
      = ∑ y ∈ (Finset.range (k + 1)).sigma (fun p => Finset.range (k - p + 1)), G y.1 y.2 := by
  apply Finset.sum_nbij'
    (i := fun x : Sigma (fun _ : ℕ => ℕ) => Sigma.mk (x.1 - x.2) (k - x.1))
    (j := fun y : Sigma (fun _ : ℕ => ℕ) => Sigma.mk (k - y.2) (k - y.2 - y.1))
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have h1 : k - (x.1 - x.2) - (k - x.1) = x.2 := by omega
    have h2 : k - (k - x.1) = x.1 := by omega
    simp only [h1, h2]
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    have h1 : k - y.2 - (k - y.2 - y.1) = y.1 := by omega
    have h2 : k - (k - y.2) = y.2 := by omega
    simp only [h1, h2]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    exact hval x.1 x.2 (by omega) (by omega)
