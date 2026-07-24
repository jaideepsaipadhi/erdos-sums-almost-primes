#!/usr/bin/env python3
import sys, io

PATH = sys.argv[1] if len(sys.argv) > 1 else "Banksmartin/Basic.lean"

TOK = {
    "<<R>>":  "\u211d", "<<N>>":  "\u2115", "<<Q>>":  "\u211a",
    "<<SUM>>": "\u2211", "<<IN>>": "\u2208", "<<LE>>": "\u2264",
    "<<GE>>": "\u2265", "<<NE>>": "\u2260", "<<LF>>": "\u230a",
    "<<RF>>": "\u230b", "<<POS>>": "\u208a", "<<S0>>": "\u2080",
    "<<AND>>": "\u2227", "<<TO>>": "\u2192", "<<ALL>>": "\u2200",
    "<<EX>>": "\u2203", "<<LA>>": "\u27e8", "<<RA>>": "\u27e9",
    "<<SS>>": "\u2286", "<<LARR>>": "\u2190", "<<AL>>": "\u03b1",
}

NEW = r'''
/-- Flip helper: B <<LE>> x/3 gives 3 <<LE>> x/B (dedups a pattern used repeatedly). -/
theorem div_ge_three_of_le_third (x B : <<R>>) (hxpos : 0 < x) (hB : 0 < B)
    (h : B <<LE>> x / 3) : 3 <<LE>> x / B := by
  have heq3 : x / (x / 3) = 3 := by field_simp
  have hge : x / (x / 3) <<LE>> x / B := div_le_div_of_nonneg_left hxpos.le hB h
  linarith [heq3 \u25b8 hge]

/-- For x <<GE>> 9 we have log x <<GE>> 2, via e^2 < 7.4 < 9. -/
theorem two_le_log (x : <<R>>) (hx : 9 <<LE>> x) : (2:<<R>>) <<LE>> Real.log x := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [<<LARR>> Real.exp_add]
    norm_num
  have he2 : Real.exp 2 <<LE>> x := by
    rw [h2]
    nlinarith [(Real.exp_pos 1).le, h1, hx]
  rw [show (2:<<R>>) = Real.log (Real.exp 2) by rw [Real.log_exp]]
  exact Real.log_le_log (Real.exp_pos 2) he2

/-- For x <<GE>> 9, loglog x <<GE>> log 2. -/
theorem loglog_ge_log_two (x : <<R>>) (hx : 9 <<LE>> x) :
    Real.log 2 <<LE>> Real.log (Real.log x) := by
  have h2 := two_le_log x hx
  exact Real.log_le_log (by norm_num) (by linarith)

/-- The dyadic index J = Nat.log 2 (floor(x/3)) brackets x/3 between 2^J and 2^(J+1). -/
theorem dyadic_log_bounds (x : <<R>>) (hx : 9 <<LE>> x) :
    (2:<<R>>) ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>>) <<LE>> x / 3 <<AND>>
      x / 3 <<LE>> (2:<<R>>) ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>> + 1) := by
  have hx3 : (3:<<R>>) <<LE>> x / 3 := by linarith
  have hN : 3 <<LE>> <<LF>>x / 3<<RF>><<POS>> := Nat.le_floor (by push_cast; linarith)
  constructor
  · have h1 : (2:<<N>>) ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>>) <<LE>> <<LF>>x / 3<<RF>><<POS>> :=
      Nat.pow_log_le_self 2 (by omega)
    have h2 : (<<LF>>x / 3<<RF>><<POS>> : <<R>>) <<LE>> x / 3 := Nat.floor_le (by linarith)
    calc (2:<<R>>) ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>>)
        = ((2 ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>>) : <<N>>) : <<R>>) := by norm_cast
      _ <<LE>> (<<LF>>x / 3<<RF>><<POS>> : <<R>>) := by exact_mod_cast h1
      _ <<LE>> x / 3 := h2
  · have h1 : <<LF>>x / 3<<RF>><<POS>> < 2 ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>> + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : x / 3 < (<<LF>>x / 3<<RF>><<POS>> : <<R>>) + 1 := Nat.lt_floor_add_one _
    have h3 : (<<LF>>x / 3<<RF>><<POS>> : <<R>>) + 1
        <<LE>> ((2 ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>> + 1) : <<N>>) : <<R>>) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    calc x / 3 <<LE>> (<<LF>>x / 3<<RF>><<POS>> : <<R>>) + 1 := h2.le
      _ <<LE>> ((2 ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>> + 1) : <<N>>) : <<R>>) := h3
      _ = (2:<<R>>) ^ (Nat.log 2 <<LF>>x / 3<<RF>><<POS>> + 1) := by norm_cast

/-- If x/3 <<LE>> 2^(J+1) then (J+1)*log 2 <<GE>> (log x)/2, via sqrt x <<LE>> x/3 for x <<GE>> 9. -/
theorem log_x_half_le (x : <<R>>) (J : <<N>>) (hx : 9 <<LE>> x)
    (hJ : x / 3 <<LE>> (2:<<R>>) ^ (J + 1)) :
    Real.log x / 2 <<LE>> ((J:<<R>>) + 1) * Real.log 2 := by
  have hxpos : (0:<<R>>) < x := by linarith
  have h3sqrt : (3:<<R>>) <<LE>> Real.sqrt x := by
    rw [show (3:<<R>>) = Real.sqrt 9 by
      rw [show (9:<<R>>) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsqrt_le : Real.sqrt x <<LE>> x / 3 := by
    rw [le_div_iff<<S0>> (by norm_num : (0:<<R>>) < 3)]
    calc Real.sqrt x * 3 <<LE>> Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h3sqrt (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hxpos.le
  calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hxpos.le).symm
    _ <<LE>> Real.log ((2:<<R>>) ^ (J + 1)) :=
        Real.log_le_log (Real.sqrt_pos.mpr hxpos) (le_trans hsqrt_le hJ)
    _ = ((J:<<R>>) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        try ring

/-- If 2^J <<LE>> x then J+1 <<LE>> 2*log x, for x <<GE>> 9. -/
theorem J_le_two_log (x : <<R>>) (J : <<N>>) (hx : 9 <<LE>> x)
    (hJ : (2:<<R>>) ^ J <<LE>> x) : ((J:<<R>>) + 1) <<LE>> 2 * Real.log x := by
  have hlogx2 := two_le_log x hx
  have hJlog : (J:<<R>>) * Real.log 2 <<LE>> Real.log x := by
    calc (J:<<R>>) * Real.log 2 = Real.log ((2:<<R>>) ^ J) := (Real.log_pow J 2).symm
      _ <<LE>> Real.log x := Real.log_le_log (by positivity) hJ
  have hlog2_23 : (2:<<R>>) / 3 <<LE>> Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hJle : (J:<<R>>) <<LE>> (3 / 2) * Real.log x := by
    have h1 : (J:<<R>>) * ((2:<<R>>) / 3) <<LE>> (J:<<R>>) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2_23 (by positivity)
    nlinarith [hJlog]
  linarith [hJle, hlogx2]

/-- The final constant absorption: 1 + log(J+1) <<LE>> 4*loglog x when J+1 <<LE>> 2*log x. -/
theorem one_add_log_le_loglog (x : <<R>>) (J : <<N>>) (hx : 9 <<LE>> x)
    (hJ2 : ((J:<<R>>) + 1) <<LE>> 2 * Real.log x) :
    1 + Real.log ((J:<<R>>) + 1) <<LE>> 4 * Real.log (Real.log x) := by
  have hlogx2 := two_le_log x hx
  have hloglog := loglog_ge_log_two x hx
  have hJ1pos : (0:<<R>>) < (J:<<R>>) + 1 := by positivity
  have hA : Real.log ((J:<<R>>) + 1) <<LE>> Real.log 2 + Real.log (Real.log x) := by
    calc Real.log ((J:<<R>>) + 1) <<LE>> Real.log (2 * Real.log x) :=
          Real.log_le_log hJ1pos hJ2
      _ = Real.log 2 + Real.log (Real.log x) := Real.log_mul (by norm_num) (by linarith)
  have hB : (1:<<R>>) <<LE>> 2 * Real.log 2 := by
    have he : Real.exp 1 <<LE>> 4 := by linarith [Real.exp_one_lt_d9]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:<<R>>) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc (1:<<R>>) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <<LE>> Real.log 4 := Real.log_le_log (Real.exp_pos 1) he
      _ = 2 * Real.log 2 := h4
  linarith [hA, hB, hloglog]

/-- Low dyadic range (j <<LE>> M, 2M <<LE>> J): harmonic bound with the (log x)/2 floor. -/
theorem dyadic_low_sum (x : <<R>>) (J M : <<N>>) (hx : 9 <<LE>> x) (hM : 2 * M <<LE>> J)
    (hJ : (2:<<R>>) ^ J <<LE>> x) :
    <<SUM>> j <<IN>> Finset.range (M + 1), 1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      <<LE>> 2 / Real.log x * (1 + Real.log ((M:<<R>>) + 1)) := by
  have hxpos : (0:<<R>>) < x := by linarith
  have hlogx_pos : (0:<<R>>) < Real.log x := Real.log_pos (by linarith)
  have hc_nonneg : (0:<<R>>) <<LE>> 2 / Real.log x := by positivity
  have hterm : <<ALL>> j <<IN>> Finset.range (M + 1),
      1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
        <<LE>> 2 / Real.log x * (1 / ((j:<<R>>) + 1)) := by
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hsq : ((2:<<R>>) ^ j) ^ 2 <<LE>> x := by
      have h1 : ((2:<<R>>) ^ j) ^ 2 = (2:<<R>>) ^ (j * 2) := (pow_mul 2 j 2).symm
      rw [h1]
      calc (2:<<R>>) ^ (j * 2) <<LE>> (2:<<R>>) ^ J := by
            apply pow_le_pow_right<<S0>> (by norm_num)
            omega
        _ <<LE>> x := hJ
    have hlow := log_ratio_low x j hx hsq
    have hj1 : (0:<<R>>) < (j:<<R>>) + 1 := by positivity
    have hden1 : (0:<<R>>) < ((j:<<R>>) + 1) * (Real.log x / 2) := by positivity
    have hmono : ((j:<<R>>) + 1) * (Real.log x / 2)
        <<LE>> ((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j) :=
      mul_le_mul_of_nonneg_left hlow hj1.le
    have h1 := one_div_le_one_div_of_le hden1 hmono
    have h2 : 1 / (((j:<<R>>) + 1) * (Real.log x / 2))
        = 2 / Real.log x * (1 / ((j:<<R>>) + 1)) := by
      have hne1 : ((j:<<R>>) + 1) <<NE>> 0 := hj1.ne'
      have hne2 : Real.log x <<NE>> 0 := hlogx_pos.ne'
      field_simp
      try ring
    calc 1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
        <<LE>> 1 / (((j:<<R>>) + 1) * (Real.log x / 2)) := h1
      _ = 2 / Real.log x * (1 / ((j:<<R>>) + 1)) := h2
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : <<SUM>> j <<IN>> Finset.range (M + 1), 2 / Real.log x * (1 / ((j:<<R>>) + 1))
      = 2 / Real.log x * <<SUM>> j <<IN>> Finset.range (M + 1), (1 / ((j:<<R>>) + 1)) := by
    rw [Finset.mul_sum]
  have hharm := harmonic_sum_le (M + 1)
  have hcastlog : Real.log ((M + 1 : <<N>>) : <<R>>) = Real.log ((M:<<R>>) + 1) := by norm_cast
  calc <<SUM>> j <<IN>> Finset.range (M + 1),
      1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      <<LE>> <<SUM>> j <<IN>> Finset.range (M + 1), 2 / Real.log x * (1 / ((j:<<R>>) + 1)) := hsum1
    _ = 2 / Real.log x * <<SUM>> j <<IN>> Finset.range (M + 1), (1 / ((j:<<R>>) + 1)) := hsum2
    _ <<LE>> 2 / Real.log x * (1 + Real.log ((M:<<R>>) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nonneg
        calc <<SUM>> i <<IN>> Finset.range (M + 1), (1:<<R>>) / ((i:<<R>>) + 1)
            <<LE>> 1 + Real.log ((M + 1 : <<N>>) : <<R>>) := hharm
          _ = 1 + Real.log ((M:<<R>>) + 1) := by rw [hcastlog]

/-- High dyadic range (M < j <<LE>> J, J <<LE>> 2M+1): reflected harmonic bound. -/
theorem dyadic_high_sum (x : <<R>>) (J M : <<N>>) (hx : 9 <<LE>> x) (hJM : J <<LE>> 2 * M + 1)
    (hJ3 : (2:<<R>>) ^ J <<LE>> x / 3) :
    <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1),
        1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      <<LE>> 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 + Real.log ((J:<<R>>) + 1)) := by
  have hxpos : (0:<<R>>) < x := by linarith
  have hlog2_pos : (0:<<R>>) < Real.log 2 := Real.log_pos (by norm_num)
  have hJ1pos : (0:<<R>>) < (J:<<R>>) + 1 := by positivity
  have hc_nonneg : (0:<<R>>) <<LE>> 2 / (((J:<<R>>) + 1) * Real.log 2) := by positivity
  have hterm : <<ALL>> j <<IN>> Finset.Ico (M + 1) (J + 1),
      1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
        <<LE>> 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 / (((J - j : <<N>>) : <<R>>) + 1)) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hjJ : j <<LE>> J := by omega
    have h2jpos : (0:<<R>>) < (2:<<R>>) ^ j := by positivity
    have h2Jpos : (0:<<R>>) < (2:<<R>>) ^ J := by positivity
    have hx2J : (3:<<R>>) <<LE>> x / (2:<<R>>) ^ J :=
      div_ge_three_of_le_third x ((2:<<R>>) ^ J) hxpos h2Jpos hJ3
    have hsplit : x / (2:<<R>>) ^ j = (x / (2:<<R>>) ^ J) * (2:<<R>>) ^ (J - j) := by
      have hpow : (2:<<R>>) ^ J = (2:<<R>>) ^ j * (2:<<R>>) ^ (J - j) := by
        rw [<<LARR>> pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
      try ring
    have hx2j_ge : (2:<<R>>) ^ ((J - j) + 1) <<LE>> x / (2:<<R>>) ^ j := by
      rw [hsplit, pow_succ]
      have h2 : (2:<<R>>) <<LE>> x / (2:<<R>>) ^ J := by linarith
      calc (2:<<R>>) ^ (J - j) * 2 <<LE>> (2:<<R>>) ^ (J - j) * (x / (2:<<R>>) ^ J) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (x / (2:<<R>>) ^ J) * (2:<<R>>) ^ (J - j) := mul_comm _ _
    have hlog_ge : ((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2
        <<LE>> Real.log (x / (2:<<R>>) ^ j) := by
      have h1 : Real.log ((2:<<R>>) ^ ((J - j) + 1))
          = ((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        try ring
      calc ((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2
          = Real.log ((2:<<R>>) ^ ((J - j) + 1)) := h1.symm
        _ <<LE>> Real.log (x / (2:<<R>>) ^ j) := Real.log_le_log (by positivity) hx2j_ge
    have hfrac : ((J:<<R>>) + 1) / 2 <<LE>> (j:<<R>>) + 1 := by
      have hn : J + 1 <<LE>> 2 * (j + 1) := by omega
      have hcast := (Nat.cast_le (<<AL>> := <<R>>)).mpr hn
      push_cast at hcast
      linarith
    have hlog_pos_j : (0:<<R>>) < Real.log (x / (2:<<R>>) ^ j) := by
      have h1 : (0:<<R>>) < ((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2 := by positivity
      linarith [hlog_ge]
    have hden_lower : (0:<<R>>) 
        ((J:<<R>>) + 1) / 2 * (((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2) := by
      positivity
    have hden_ge : ((J:<<R>>) + 1) / 2 * (((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2)
        <<LE>> ((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j) :=
      mul_le_mul hfrac hlog_ge (by positivity) (by positivity)
    have h1 := one_div_le_one_div_of_le hden_lower hden_ge
    have h2 : 1 / (((J:<<R>>) + 1) / 2 * (((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2))
        = 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 / (((J - j : <<N>>) : <<R>>) + 1)) := by
      have hne1 : ((J:<<R>>) + 1) <<NE>> 0 := hJ1pos.ne'
      have hne2 : Real.log 2 <<NE>> 0 := hlog2_pos.ne'
      have hne3 : ((((J - j : <<N>>) : <<R>>)) + 1) <<NE>> 0 := by positivity
      field_simp
      try ring
    calc 1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
        <<LE>> 1 / (((J:<<R>>) + 1) / 2 * (((((J - j : <<N>>) : <<R>>)) + 1) * Real.log 2)) := h1
      _ = 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 / (((J - j : <<N>>) : <<R>>) + 1)) := h2
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1),
      2 / (((J:<<R>>) + 1) * Real.log 2) * (1 / (((J - j : <<N>>) : <<R>>) + 1))
      = 2 / (((J:<<R>>) + 1) * Real.log 2) *
        <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1), (1 / (((J - j : <<N>>) : <<R>>) + 1)) := by
    rw [Finset.mul_sum]
  have hsub : Finset.Ico (M + 1) (J + 1) <<SS>> Finset.range (J + 1) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl
  have hsum3 : <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1), (1 / (((J - j : <<N>>) : <<R>>) + 1))
      <<LE>> <<SUM>> j <<IN>> Finset.range (J + 1), (1 / (((J - j : <<N>>) : <<R>>) + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  have hreflect : <<SUM>> j <<IN>> Finset.range (J + 1),
      (1:<<R>>) / (((J - j : <<N>>) : <<R>>) + 1)
      = <<SUM>> i <<IN>> Finset.range (J + 1), (1:<<R>>) / ((i:<<R>>) + 1) := by
    rw [<<LARR>> Finset.sum_range_reflect (fun i => (1:<<R>>) / ((i:<<R>>) + 1)) (J + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjj : J + 1 - 1 - j = J - j := by omega
    rw [hjj]
  have hharm := harmonic_sum_le (J + 1)
  have hcastlog : Real.log ((J + 1 : <<N>>) : <<R>>) = Real.log ((J:<<R>>) + 1) := by norm_cast
  calc <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1),
      1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      <<LE>> <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1),
        2 / (((J:<<R>>) + 1) * Real.log 2) * (1 / (((J - j : <<N>>) : <<R>>) + 1)) := hsum1
    _ = 2 / (((J:<<R>>) + 1) * Real.log 2) *
        <<SUM>> j <<IN>> Finset.Ico (M + 1) (J + 1), (1 / (((J - j : <<N>>) : <<R>>) + 1)) := hsum2
    _ <<LE>> 2 / (((J:<<R>>) + 1) * Real.log 2) *
        <<SUM>> j <<IN>> Finset.range (J + 1), (1 / (((J - j : <<N>>) : <<R>>) + 1)) :=
        mul_le_mul_of_nonneg_left hsum3 hc_nonneg
    _ = 2 / (((J:<<R>>) + 1) * Real.log 2) *
        <<SUM>> i <<IN>> Finset.range (J + 1), (1 / ((i:<<R>>) + 1)) := by rw [hreflect]
    _ <<LE>> 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 + Real.log ((J:<<R>>) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nonneg
        calc <<SUM>> i <<IN>> Finset.range (J + 1), (1:<<R>>) / ((i:<<R>>) + 1)
            <<LE>> 1 + Real.log ((J + 1 : <<N>>) : <<R>>) := hharm
          _ = 1 + Real.log ((J:<<R>>) + 1) := by rw [hcastlog]

'''

ANCHOR = "/-- THE dyadic sum bound"

def main():
    with io.open(PATH, "r", encoding="utf-8") as fh:
        s = fh.read()
    if "theorem dyadic_high_sum" in s:
        print("ERROR: patch already applied; aborting."); sys.exit(1)
    i = s.find(ANCHOR)
    if i < 0:
        print("ERROR: anchor docstring not found; aborting."); sys.exit(1)
    if s.find(ANCHOR, i + 1) >= 0:
        print("ERROR: anchor appears twice; aborting."); sys.exit(1)
    new = NEW
    for k, v in TOK.items():
        new = new.replace(k, v)
    new = new.replace("\\u25b8", "\u25b8")
    if "<<" in new:
        print("ERROR: unreplaced token remains; aborting."); sys.exit(1)
    out = s[:i] + new.lstrip("\n") + "\n" + s[i:]
    with io.open(PATH, "w", encoding="utf-8") as fh:
        fh.write(out)
    print("OK: inserted before sum_ratio_log_dyadic.")
    for name in ["div_ge_three_of_le_third", "two_le_log", "loglog_ge_log_two",
                 "dyadic_log_bounds", "log_x_half_le", "J_le_two_log",
                 "one_add_log_le_loglog", "dyadic_low_sum", "dyadic_high_sum"]:
        print("  ", name, "present:", ("theorem " + name) in out)

if __name__ == "__main__":
    main()
