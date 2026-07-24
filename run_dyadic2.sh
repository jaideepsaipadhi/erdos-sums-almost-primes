#!/usr/bin/env bash
set -u

echo "===== STEP 1: primeCounting_le_bound_own statement+proof ====="
sed -n '/^theorem primeCounting_le_bound_own/,/^theorem piK_bound_one/p' Banksmartin/Basic.lean

echo "===== STEP 2: integral_term_bound_gen body (missing from last paste) ====="
sed -n '/^theorem integral_term_bound_gen/,/^theorem integral_term_bound (/p' Banksmartin/Basic.lean

echo "===== STEP 3: writing patch_dyadic2.py ====="
cat > patch_dyadic2.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io

PATH = sys.argv[1] if len(sys.argv) > 1 else "Banksmartin/Basic.lean"

TOK = {
    "<<R>>":  "\u211d", "<<N>>":  "\u2115", "<<SUM>>": "\u2211",
    "<<IN>>": "\u2208", "<<LE>>": "\u2264", "<<GE>>": "\u2265",
    "<<NE>>": "\u2260", "<<LF>>": "\u230a", "<<RF>>": "\u230b",
    "<<POS>>": "\u208a", "<<S0>>": "\u2080", "<<AND>>": "\u2227",
    "<<TO>>": "\u2192", "<<ALL>>": "\u2200", "<<EX>>": "\u2203",
    "<<LA>>": "\u27e8", "<<RA>>": "\u27e9", "<<SS>>": "\u2286",
    "<<EMPTY>>": "\u2205",
}

NEW = r'''
/-- Fiber j = 0 is empty: every k in `Ioc p<<S0>> N` has k <<GE>> 2, hence `Nat.log 2 k <<GE>> 1`. -/
theorem dyadic_fiber_zero_empty (p<<S0>> N : <<N>>) (hp<<S0>> : 1 <<LE>> p<<S0>>) :
    (Finset.Ioc p<<S0>> N).filter (fun k => Nat.log 2 k = 0) = <<EMPTY>> := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro k hk
  simp only [Finset.mem_Ioc] at hk
  have h2k : 2 <<LE>> k := by omega
  have hpos : 0 < Nat.log 2 k := Nat.log_pos (by norm_num) h2k
  omega

/-- Per-fiber bound: on dyadic fiber j, every term is at most h(2^j) (antitone),
and the number of prime terms is at most pi(2^(j+1)). -/
theorem dyadic_fiber_sum_bound (x : <<R>>) (p<<S0>> j : <<N>>) (hp<<S0>> : 1 <<LE>> p<<S0>>)
    (hx : 9 <<LE>> x) (h2j : (2 ^ j : <<R>>) <<LE>> x / 3) :
    <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) <<LE>>
      ((x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>))) *
        (Nat.primeCounting (2 ^ (j + 1)) : <<R>>) := by
  classical
  have hxpos : (0:<<R>>) < x := by linarith
  have h2jpos : (0:<<R>>) < (2 ^ j : <<R>>) := by positivity
  have hx2j3 : (3:<<R>>) <<LE>> x / (2 ^ j : <<R>>) := by
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) <<LE>> x / (2 ^ j : <<R>>) :=
      div_le_div_of_nonneg_left hxpos.le h2jpos h2j
    linarith [heq3 \u25b8 hge]
  have hlogpos : 0 < Real.log (x / (2 ^ j : <<R>>)) := Real.log_pos (by linarith)
  have hb_nonneg : 0 <<LE>> (x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>)) :=
    div_nonneg (div_nonneg hxpos.le h2jpos.le) hlogpos.le
  have h1le2j : (1:<<R>>) <<LE>> (2 ^ j : <<R>>) := by
    exact_mod_cast Nat.one_le_two_pow
  have hstep1 : <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
      ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>)
      = <<SUM>> k <<IN>> ((Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j)).filter
          (fun k => Nat.Prime k), ((x / k) / Real.log (x / k)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hP : Nat.Prime k
    · simp [hP]
    · simp [hP]
  have hanti := ratio_log_antitoneOn x (by linarith)
  have hterm : <<ALL>> k <<IN>> ((Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j)).filter
      (fun k => Nat.Prime k),
      ((x / k) / Real.log (x / k)) <<LE>>
        ((x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>))) := by
    intro k hk
    obtain <<LA>>hkS, hkp<<RA>> := Finset.mem_filter.mp hk
    have hb := dyadic_fiber_mem_bounds p<<S0>> <<LF>>x / 3<<RF>><<POS>> j k hkS
    obtain <<LA>>hkmem, hkj<<RA>> := Finset.mem_filter.mp hkS
    simp only [Finset.mem_Ioc] at hkmem
    have hk2 : 2 <<LE>> k := by omega
    have hk1R : (1:<<R>>) <<LE>> (k : <<R>>) := by exact_mod_cast (by omega : 1 <<LE>> k)
    have hkfloor : (k : <<R>>) <<LE>> (<<LF>>x / 3<<RF>><<POS>> : <<R>>) := by exact_mod_cast hkmem.2
    have hfloorle : (<<LF>>x / 3<<RF>><<POS>> : <<R>>) <<LE>> x / 3 := Nat.floor_le (by linarith)
    have hkleR : (k : <<R>>) <<LE>> x / 3 := by linarith
    have h2jkR : (2 ^ j : <<R>>) <<LE>> (k : <<R>>) := by exact_mod_cast hb.1
    have hmono := hanti (Set.mem_Icc.mpr <<LA>>h1le2j, h2j<<RA>>)
      (Set.mem_Icc.mpr <<LA>>hk1R, hkleR<<RA>>) h2jkR
    simpa using hmono
  have hsum_le := Finset.sum_le_card_nsmul
    (((Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j)).filter
      (fun k => Nat.Prime k))
    (fun k => ((x / k) / Real.log (x / k)))
    ((x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>))) hterm
  rw [nsmul_eq_mul] at hsum_le
  have hcard := dyadic_fiber_prime_card p<<S0>> <<LF>>x / 3<<RF>><<POS>> j
  calc <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j),
      ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>)
      = <<SUM>> k <<IN>> ((Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j)).filter
          (fun k => Nat.Prime k), ((x / k) / Real.log (x / k)) := hstep1
    _ <<LE>> ((((Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>).filter (fun k => Nat.log 2 k = j)).filter
          (fun k => Nat.Prime k)).card : <<R>>) *
        ((x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>))) := hsum_le
    _ <<LE>> (Nat.primeCounting (2 ^ (j + 1)) : <<R>>) *
        ((x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>))) :=
      mul_le_mul_of_nonneg_right hcard hb_nonneg
    _ = ((x / (2 ^ j : <<R>>)) / Real.log (x / (2 ^ j : <<R>>))) *
        (Nat.primeCounting (2 ^ (j + 1)) : <<R>>) := mul_comm _ _

'''

ANCHOR = "/-- THE dyadic sum bound"

def main():
    with io.open(PATH, "r", encoding="utf-8") as fh:
        s = fh.read()
    if "theorem dyadic_fiber_sum_bound" in s:
        print("ERROR: dyadic_fiber_sum_bound already present; aborting."); sys.exit(1)
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
    for name in ["dyadic_fiber_zero_empty", "dyadic_fiber_sum_bound"]:
        print("  ", name, "present:", ("theorem " + name) in out)

if __name__ == "__main__":
    main()
PYEOF

echo "===== STEP 4: applying patch ====="
python3 patch_dyadic2.py

echo "===== STEP 5: lake build ====="
lake build
