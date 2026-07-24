#!/usr/bin/env bash
set -u

echo "===== STEP 1: writing patch_dyadic4.py ====="
cat > patch_dyadic4.py << 'PYEOF'
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
    "<<SS>>": "\u2286", "<<LARR>>": "\u2190",
}

NEW = r'''
/-- Chebyshev specialized to powers of two: pi(2^(j+1)) <<LE>> 8*2^(j+1)/(j+1).
The sqrt term is absorbed via sqrt(n)*log(sqrt(n)) <<LE>> n and log 2 > 1/2. -/
theorem primeCounting_two_pow_bound (j : <<N>>) (hj : 1 <<LE>> j) :
    (Nat.primeCounting (2 ^ (j + 1)) : <<R>>) <<LE>> 8 * 2 ^ (j + 1) / (j + 1) := by
  have hn4 : 4 <<LE>> 2 ^ (j + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ <<LE>> 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmain := primeCounting_le_bound_own (2 ^ (j + 1)) hn4
  have hcast : ((2 ^ (j + 1) : <<N>>) : <<R>>) = (2:<<R>>) ^ (j + 1) := by norm_cast
  rw [hcast] at hmain
  have h2pos : (0:<<R>>) < (2:<<R>>) ^ (j + 1) := by positivity
  have hj1pos : (0:<<R>>) < (j:<<R>>) + 1 := by positivity
  have hlog2pos : (0:<<R>>) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsqrt : Real.log (Real.sqrt ((2:<<R>>) ^ (j + 1)))
      = ((j:<<R>>) + 1) * Real.log 2 / 2 := by
    rw [Real.log_sqrt h2pos.le, Real.log_pow]
    push_cast
    try ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:<<R>>) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hterm2 : (2:<<R>>) ^ (j + 1) * Real.log 4 / Real.log (Real.sqrt ((2:<<R>>) ^ (j + 1)))
      = 4 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1) := by
    rw [hlogsqrt, hlog4]
    have hne1 : ((j:<<R>>) + 1) <<NE>> 0 := hj1pos.ne'
    have hne2 : Real.log 2 <<NE>> 0 := hlog2pos.ne'
    field_simp
    try ring
  have hs_nonneg : 0 <<LE>> Real.sqrt ((2:<<R>>) ^ (j + 1)) := Real.sqrt_nonneg _
  have hlog2_half : (1:<<R>>)/2 <<LE>> Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hsqrt_bound : Real.sqrt ((2:<<R>>) ^ (j + 1))
      <<LE>> 4 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1) := by
    have hlog_le : Real.log (Real.sqrt ((2:<<R>>) ^ (j + 1)))
        <<LE>> Real.sqrt ((2:<<R>>) ^ (j + 1)) := Real.log_le_self hs_nonneg
    have hsq : Real.sqrt ((2:<<R>>) ^ (j + 1)) * Real.sqrt ((2:<<R>>) ^ (j + 1))
        = (2:<<R>>) ^ (j + 1) := Real.mul_self_sqrt h2pos.le
    have hkey : Real.sqrt ((2:<<R>>) ^ (j + 1)) * (((j:<<R>>) + 1) * Real.log 2 / 2)
        <<LE>> (2:<<R>>) ^ (j + 1) := by
      rw [<<LARR>> hlogsqrt]
      calc Real.sqrt ((2:<<R>>) ^ (j + 1)) * Real.log (Real.sqrt ((2:<<R>>) ^ (j + 1)))
          <<LE>> Real.sqrt ((2:<<R>>) ^ (j + 1)) * Real.sqrt ((2:<<R>>) ^ (j + 1)) :=
            mul_le_mul_of_nonneg_left hlog_le hs_nonneg
        _ = (2:<<R>>) ^ (j + 1) := hsq
    rw [le_div_iff<<S0>> hj1pos]
    nlinarith [hkey, hs_nonneg, hj1pos, hlog2_half,
      mul_nonneg (mul_nonneg hs_nonneg hj1pos.le) (sub_nonneg.mpr hlog2_half)]
  rw [hterm2] at hmain
  have h48 : 4 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1) + 4 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1)
      = 8 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1) := by ring
  push_cast
  linarith [hmain, hsqrt_bound, h48]

/-- Per-fiber constant simplification:
h(2^j) * pi(2^(j+1)) <<LE>> 16*x / ((j+1) * log(x/2^j)). -/
theorem dyadic_term_bound (x : <<R>>) (j : <<N>>) (hj : 1 <<LE>> j) (hx : 9 <<LE>> x)
    (h2j : (2:<<R>>) ^ j <<LE>> x / 3) :
    ((x / (2:<<R>>) ^ j) / Real.log (x / (2:<<R>>) ^ j)) *
        (Nat.primeCounting (2 ^ (j + 1)) : <<R>>) <<LE>>
      16 * x / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := by
  have hxpos : (0:<<R>>) < x := by linarith
  have h2jpos : (0:<<R>>) < (2:<<R>>) ^ j := by positivity
  have hx2j3 : (3:<<R>>) <<LE>> x / (2:<<R>>) ^ j := by
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) <<LE>> x / (2:<<R>>) ^ j :=
      div_le_div_of_nonneg_left hxpos.le h2jpos h2j
    linarith [heq3 \u25b8 hge]
  have hlogpos : (0:<<R>>) < Real.log (x / (2:<<R>>) ^ j) := Real.log_pos (by linarith)
  have hj1pos : (0:<<R>>) < (j:<<R>>) + 1 := by positivity
  have hh_nonneg : (0:<<R>>) <<LE>> (x / (2:<<R>>) ^ j) / Real.log (x / (2:<<R>>) ^ j) :=
    div_nonneg (by positivity) hlogpos.le
  have hpc := primeCounting_two_pow_bound j hj
  push_cast at hpc
  have hid : ((x / (2:<<R>>) ^ j) / Real.log (x / (2:<<R>>) ^ j)) *
      (8 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1))
      = 16 * x / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := by
    have hne1 : ((j:<<R>>) + 1) <<NE>> 0 := hj1pos.ne'
    have hne2 : Real.log (x / (2:<<R>>) ^ j) <<NE>> 0 := hlogpos.ne'
    have hne3 : (2:<<R>>) ^ j <<NE>> 0 := h2jpos.ne'
    rw [pow_succ]
    field_simp
    try ring
  calc ((x / (2:<<R>>) ^ j) / Real.log (x / (2:<<R>>) ^ j)) *
      (Nat.primeCounting (2 ^ (j + 1)) : <<R>>)
      <<LE>> ((x / (2:<<R>>) ^ j) / Real.log (x / (2:<<R>>) ^ j)) *
        (8 * (2:<<R>>) ^ (j + 1) / ((j:<<R>>) + 1)) :=
        mul_le_mul_of_nonneg_left hpc hh_nonneg
    _ = 16 * x / (((j:<<R>>) + 1) * Real.log (x / (2:<<R>>) ^ j)) := hid

/-- On the low dyadic range ((2^j)^2 <<LE>> x): log(x/2^j) <<GE>> (log x)/2. -/
theorem log_ratio_low (x : <<R>>) (j : <<N>>) (hx : 9 <<LE>> x)
    (hsq : ((2:<<R>>) ^ j) ^ 2 <<LE>> x) :
    Real.log x / 2 <<LE>> Real.log (x / (2:<<R>>) ^ j) := by
  have hxpos : (0:<<R>>) < x := by linarith
  have h2jpos : (0:<<R>>) < (2:<<R>>) ^ j := by positivity
  have h2j_le_sqrt : (2:<<R>>) ^ j <<LE>> Real.sqrt x := by
    rw [show ((2:<<R>>) ^ j) = Real.sqrt (((2:<<R>>) ^ j) ^ 2) by
      rw [Real.sqrt_sq h2jpos.le]]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hdiv : Real.sqrt x <<LE>> x / (2:<<R>>) ^ j := by
    rw [le_div_iff<<S0>> h2jpos]
    calc Real.sqrt x * (2:<<R>>) ^ j <<LE>> Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h2j_le_sqrt hsqrt_pos.le
      _ = x := Real.mul_self_sqrt hxpos.le
  calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hxpos.le).symm
    _ <<LE>> Real.log (x / (2:<<R>>) ^ j) := Real.log_le_log hsqrt_pos hdiv

/-- Harmonic sum bound, real form: sum_(i<n) 1/(i+1) <<LE>> 1 + log n. -/
theorem harmonic_sum_le (n : <<N>>) :
    <<SUM>> i <<IN>> Finset.range n, (1:<<R>>) / ((i:<<R>>) + 1) <<LE>> 1 + Real.log n := by
  have heq : ((harmonic n : <<Q>>) : <<R>>)
      = <<SUM>> i <<IN>> Finset.range n, (1:<<R>>) / ((i:<<R>>) + 1) := by
    unfold harmonic
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div]
  rw [<<LARR>> heq]
  exact harmonic_le_one_add_log n

'''

ANCHOR = "/-- THE dyadic sum bound"

def main():
    with io.open(PATH, "r", encoding="utf-8") as fh:
        s = fh.read()
    if "theorem primeCounting_two_pow_bound" in s:
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
    for name in ["primeCounting_two_pow_bound", "dyadic_term_bound",
                 "log_ratio_low", "harmonic_sum_le"]:
        print("  ", name, "present:", ("theorem " + name) in out)

if __name__ == "__main__":
    main()
PYEOF

echo "===== STEP 2: applying patch ====="
python3 patch_dyadic4.py

echo "===== STEP 3: lake build ====="
lake build
