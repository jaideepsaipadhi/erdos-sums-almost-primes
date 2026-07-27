theorem prop_2_5 (k : ℕ) (hk : 1 ≤ k) :
    Ek k = -(Real.log 2 / 4) * (2 * (k : ℝ) * Uk k - Vk k)
             - DeltaConv k - E1k k + Eexpk k := by
  have hlem21 : f k = Ik k + Tk k := lemma1_foundation k hk (fk_summable k hk)
  have hexp := Ikfrozen_re_expand k
  have h2k : ((2:ℝ) ^ k) ≠ 0 := by positivity
  have hIk : Ik k = Dk k + (Ikfrozen k).re := by
    unfold Dk
    ring
  unfold Ek E1k Eexpk aOneConst
  rw [hlem21, hIk, hexp]
  unfold Dk
  field_simp
  ring
