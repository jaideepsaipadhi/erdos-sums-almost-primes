/-- The cFac family is multipliable for s > 1.
Needed because 0 < cFac s has been threaded as a hypothesis throughout;
without multipliability that would be an assumption about a tprod junk value. -/
theorem cFac_multipliable (s : ℝ) (hs : 1 < s) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹) := by
  have hthird : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      ((p:ℕ):ℝ) ^ (-s) ≤ 1/3 := by
    intro p
    have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
    have h1 : ((p:ℕ):ℝ) ^ (-s) ≤ ((p:ℕ):ℝ) ^ (-(1:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : (((p:ℕ):ℝ))⁻¹ ≤ 1/3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (0:ℝ) < ((p:ℕ):ℝ) ^ (-s) := by
    intro p
    have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.2
    positivity
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (3/2) * (((p:ℕ):ℝ) ^ (-s))) := by
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-s)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (hbase.subtype _).mul_left _
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹ - 1) := by
    apply Summable.of_nonneg_of_le _ _ hcomp
    · intro p
      have h3 := hthird p
      have hp := hpos p
      have hden : (0:ℝ) < 1 - ((p:ℕ):ℝ) ^ (-s) := by linarith
      rw [sub_nonneg, le_inv_comm₀ (by norm_num) hden]
      linarith
    · intro p
      have h3 := hthird p
      have hp := hpos p
      have hden : (0:ℝ) < 1 - ((p:ℕ):ℝ) ^ (-s) := by linarith
      have hkey : (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹ - 1
          = ((p:ℕ):ℝ) ^ (-s) / (1 - ((p:ℕ):ℝ) ^ (-s)) := by
        field_simp
      rw [hkey, div_le_iff₀ hden]
      nlinarith
  have h := Real.multipliable_one_add_of_summable hsum
  apply h.congr
  intro p
  ring
