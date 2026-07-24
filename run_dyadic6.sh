#!/usr/bin/env bash
set -u

echo "===== STEP 1: writing patch_dyadic6.py ====="
cat > patch_dyadic6.py << 'PYEOF'
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
/-- Core of the dyadic bound, parametrized by the bracketing index J:
if 2^J <<LE>> x/3 <<LE>> 2^(J+1), the fiberwise double sum is at most 384*x*loglog x/log x. -/
theorem sum_ratio_log_dyadic_core (x : <<R>>) (p<<S0>> J : <<N>>) (hp<<S0>> : 1 <<LE>> p<<S0>>)
    (hx : 9 <<LE>> x) (h2J3 : (2:<<R>>) ^ J <<LE>> x / 3)
    (hJ13 : x / 3 <<LE>> (2:<<R>>) ^ (J + 1)) :
    <<SUM>> j <<IN>> Finset.range (J + 1),
        <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) <<LE>>
      384 * x * Real.log (Real.log x) / Real.log x := by
  have hxpos : (0:<<R>>) < x := by linarith
  have hlogx2 := two_le_log x hx
  have hlogx_pos : (0:<<R>>) < Real.log x := by linarith
  have hloglog_pos : (0:<<R>>) < Real.log (Real.log x) := Real.log_pos (by linarith)
  have h2J : (2:<<R>>) ^ J <<LE>> x := by linarith
  have hterm : <<ALL>> j <<IN>> Finset.range (J + 1),
      <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) <<LE>>
        16 * x / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := by
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have h2j : (2:<<R>>) ^ j <<LE>> x / 3 := by
      calc (2:<<R>>) ^ j <<LE>> (2:<<R>>) ^ J := by
            apply pow_le_pow_right<<S0>> (by norm_num)
            exact hj
        _ <<LE>> x / 3 := h2J3
    have hx2j3 : (3:<<R>>) <<LE>> x / (2:<<R>>) ^ j :=
      div_ge_three_of_le_third x ((2:<<R>>) ^ j) hxpos (by positivity) h2j
    have hlogj_pos : (0:<<R>>) < Real.log (x / (2:<<R>>) ^ j) := Real.log_pos (by linarith)
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [dyadic_fiber_zero_empty p<<S0>> <<LF>>x / 3<<RF>><<POS>> hp<<S0>>, Finset.sum_empty]
      have hden : (0:<<R>>) < (((0:<<N>>):<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ (0:<<N>>)) :=
        mul_pos (by positivity) hlogj_pos
      exact div_nonneg (by linarith) hden.le
    · exact le_trans (dyadic_fiber_sum_bound x p<<S0>> j hp<<S0>> hx h2j)
        (dyadic_term_bound x j hjpos hx h2j)
  have hsum1 := Finset.sum_le_sum hterm
  have hfactor : <<SUM>> j <<IN>> Finset.range (J + 1),
      16 * x / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      = 16 * x * <<SUM>> j <<IN>> Finset.range (J + 1),
          1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsplit : <<SUM>> j <<IN>> Finset.range (J + 1),
      (1:<<R>>) / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      = (<<SUM>> j <<IN>> Finset.range (J / 2 + 1),
          (1:<<R>>) / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)))
        + <<SUM>> j <<IN>> Finset.Ico (J / 2 + 1) (J + 1),
            (1:<<R>>) / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (J / 2 + 1)) (by omega)).symm
  have hlow := dyadic_low_sum x J (J / 2) hx (by omega) h2J
  have hhigh := dyadic_high_sum x J (J / 2) hx (by omega) h2J3
  have hhalf := log_x_half_le x J hx hJ13
  have hJ2 := J_le_two_log x J hx h2J
  have habs := one_add_log_le_loglog x J hx hJ2
  have hM_log : 1 + Real.log (((J / 2 : <<N>>):<<R>>) + 1) <<LE>> 4 * Real.log (Real.log x) := by
    have hle : (J / 2 : <<N>>) <<LE>> J := Nat.div_le_self J 2
    have h1 : (((J / 2 : <<N>>):<<R>>) + 1) <<LE>> ((J:<<R>>) + 1) := by
      have hc := (Nat.cast_le (<<AL>> := <<R>>)).mpr hle
      linarith
    have h2 : Real.log (((J / 2 : <<N>>):<<R>>) + 1) <<LE>> Real.log ((J:<<R>>) + 1) :=
      Real.log_le_log (by positivity) h1
    linarith [habs]
  have hhigh_coef : 2 / (((J:<<R>>) + 1) * Real.log 2) <<LE>> 4 / Real.log x := by
    have hlogx_ne : Real.log x <<NE>> 0 := hlogx_pos.ne'
    have h1 : 2 / (((J:<<R>>) + 1) * Real.log 2) <<LE>> 2 / (Real.log x / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hhalf
    have h2 : 2 / (Real.log x / 2) = 4 / Real.log x := by
      field_simp
      try ring
    calc 2 / (((J:<<R>>) + 1) * Real.log 2) <<LE>> 2 / (Real.log x / 2) := h1
      _ = 4 / Real.log x := h2
  have hc_low : (0:<<R>>) <<LE>> 2 / Real.log x := div_nonneg (by norm_num) hlogx_pos.le
  have hL2 : 2 / Real.log x * (1 + Real.log (((J / 2 : <<N>>):<<R>>) + 1))
      <<LE>> 8 * Real.log (Real.log x) / Real.log x := by
    calc 2 / Real.log x * (1 + Real.log (((J / 2 : <<N>>):<<R>>) + 1))
        <<LE>> 2 / Real.log x * (4 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_left hM_log hc_low
      _ = 8 * Real.log (Real.log x) / Real.log x := by ring
  have hH2 : 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 + Real.log ((J:<<R>>) + 1))
      <<LE>> 16 * Real.log (Real.log x) / Real.log x := by
    have h1pl : (0:<<R>>) <<LE>> 1 + Real.log ((J:<<R>>) + 1) := by
      have hln : (0:<<R>>) <<LE>> Real.log ((J:<<R>>) + 1) :=
        Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg J))
      linarith
    calc 2 / (((J:<<R>>) + 1) * Real.log 2) * (1 + Real.log ((J:<<R>>) + 1))
        <<LE>> 4 / Real.log x * (1 + Real.log ((J:<<R>>) + 1)) :=
          mul_le_mul_of_nonneg_right hhigh_coef h1pl
      _ <<LE>> 4 / Real.log x * (4 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_left habs (div_nonneg (by norm_num) hlogx_pos.le)
      _ = 16 * Real.log (Real.log x) / Real.log x := by ring
  have hU : <<SUM>> j <<IN>> Finset.range (J + 1),
      (1:<<R>>) / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j))
      <<LE>> 24 * Real.log (Real.log x) / Real.log x := by
    have h824 : 8 * Real.log (Real.log x) / Real.log x
        + 16 * Real.log (Real.log x) / Real.log x
        = 24 * Real.log (Real.log x) / Real.log x := by ring
    linarith [hsplit, hlow, hhigh, hL2, hH2, h824]
  calc <<SUM>> j <<IN>> Finset.range (J + 1),
      <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>)
      <<LE>> <<SUM>> j <<IN>> Finset.range (J + 1),
        16 * x / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := hsum1
    _ = 16 * x * <<SUM>> j <<IN>> Finset.range (J + 1),
        1 / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := hfactor
    _ <<LE>> 16 * x * (24 * Real.log (Real.log x) / Real.log x) :=
        mul_le_mul_of_nonneg_left hU (by linarith)
    _ = 384 * x * Real.log (Real.log x) / Real.log x := by ring

/-- THE dyadic sum bound, now proven: the weighted prime sum
<<SUM>>_(p prime <<LE>> x/3) (x/p)/log(x/p) is at most 384*x*loglog x/log x. -/
theorem sum_ratio_log_dyadic :
    <<EX>> K : <<R>>, 0 < K <<AND>> <<ALL>> (p<<S0>> : <<N>>) (x : <<R>>), 1 <<LE>> p<<S0>> <<TO>> 9 <<LE>> x <<TO>>
      <<SUM>> k <<IN>> Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>,
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) <<LE>>
        K * x * Real.log (Real.log x) / Real.log x := by
  refine <<LA>>384, by norm_num, fun p<<S0>> x hp<<S0>> hx => ?_<<RA>>
  obtain <<LA>>h2J3, hJ13<<RA>> := dyadic_log_bounds x hx
  calc <<SUM>> k <<IN>> Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>)
      = <<SUM>> j <<IN>> Finset.range (Nat.log 2 <<LF>>x / 3<<RF>><<POS>> + 1),
          <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
            ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) :=
        sum_dyadic_fiberwise p<<S0>> <<LF>>x / 3<<RF>><<POS>> _
    _ <<LE>> 384 * x * Real.log (Real.log x) / Real.log x :=
        sum_ratio_log_dyadic_core x p<<S0>> (Nat.log 2 <<LF>>x / 3<<RF>><<POS>>) hp<<S0>> hx h2J3 hJ13

'''

ANCHOR = "/-- THE dyadic sum bound"
END = "theorem sum_ratio_log_bound_gen"

def main():
    with io.open(PATH, "r", encoding="utf-8") as fh:
        s = fh.read()
    if "sum_ratio_log_dyadic_core" in s:
        print("ERROR: patch already applied; aborting."); sys.exit(1)
    i = s.find(ANCHOR)
    if i < 0:
        print("ERROR: anchor not found; aborting."); sys.exit(1)
    if s.find(ANCHOR, i + 1) >= 0:
        print("ERROR: anchor appears twice; aborting."); sys.exit(1)
    j = s.find(END, i)
    if j < 0:
        print("ERROR: end marker not found; aborting."); sys.exit(1)
    new = NEW
    for k, v in TOK.items():
        new = new.replace(k, v)
    if "<<" in new:
        print("ERROR: unreplaced token; aborting."); sys.exit(1)
    bad = [n + 1 for n, l in enumerate(new.split("\n")) if l.rstrip().endswith("<")]
    if bad:
        print("ERROR: payload lines end in bare <:", bad); sys.exit(1)
    out = s[:i] + new.lstrip("\n") + s[j:]
    with io.open(PATH, "w", encoding="utf-8") as fh:
        fh.write(out)
    print("OK: sorry-stub replaced with core + proven master.")
    for name in ["sum_ratio_log_dyadic_core", "sum_ratio_log_dyadic"]:
        print("  ", name, "present:", ("theorem " + name) in out)

if __name__ == "__main__":
    main()
PYEOF

echo "===== STEP 2: applying patch ====="
if python3 patch_dyadic6.py; then
  echo "===== STEP 3: lake build ====="
  lake build
else
  echo "PATCH FAILED - skipping build. Paste this whole output."
fi
