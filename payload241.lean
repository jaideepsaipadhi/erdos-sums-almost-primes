/-- The real regularised family at z = 2 is multipliable over p >= 3.
Exact algebra: (1-2/p)^(-1)(1-1/p)^2 - 1 = 1/(p(p-2)) <= 3/p^2 for p >= 3.
Without this, dConst would be an assertion about a tprod junk value. -/
theorem dConst_family_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2) := by
  have hexact : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 - 1
        = 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) := by
    intro p
    have hp3 : (3:ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
    have hp0 : (0:ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hp2 : (0:ℝ) < ((p : ℕ) : ℝ) - 2 := by linarith
    have hne : (1:ℝ) - 2 / ((p : ℕ) : ℝ) ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      field_simp at hcon
      linarith
    field_simp
    ring
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      3 * (1 / ((p : ℕ) : ℝ) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
      simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    exact (hbase.subtype _).mul_left 3
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 - 1) := by
    apply Summable.of_nonneg_of_le _ _ hcomp
    · intro p
      rw [hexact p]
      have hp3 : (3:ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
      have : (0:ℝ) < ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2) := by nlinarith
      positivity
    · intro p
      rw [hexact p]
      have hp3 : (3:ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
      rw [div_le_div_iff (by nlinarith) (by positivity)]
      nlinarith
  have h := Real.multipliable_one_add_of_summable hsum
  apply h.congr
  intro p
  ring
