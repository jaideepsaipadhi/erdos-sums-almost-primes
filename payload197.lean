/-- S(m) recovered from A_m: Definition 2.3 read backwards. -/
theorem Sm_eq_Am_div (m : ℕ) : Sm m = Am m / 2 ^ m := by
  unfold Am
  have h2 : ((2:ℝ) ^ m) ≠ 0 := by positivity
  field_simp

/-- Manuscript (3): the frozen integral, with g_i(s) replaced by c_i = g_i(1). -/
noncomputable def Ikfrozen (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), cCoeff i * ((Sm (k - i) : ℝ) : ℂ)

/-- MANUSCRIPT LEMMA 2.4 (exactness).  I'_k = sum_i c_i 2^(i-k) A_(k-i).
Every error term downstream is therefore exactly a value of the deterministic
delta, not a bound. -/
theorem Ikfrozen_eq_sum_Am (k : ℕ) :
    Ikfrozen k = ∑ i ∈ Finset.range (k + 1),
      cCoeff i * ((Am (k - i) : ℝ) : ℂ) / (2:ℂ) ^ (k - i) := by
  unfold Ikfrozen
  apply Finset.sum_congr rfl
  intro i _
  rw [Sm_eq_Am_div]
  push_cast
  ring
