#!/usr/bin/env bash
set -u

cat > patch_dyadic7r1.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io, hashlib

PATH = sys.argv[1] if len(sys.argv) > 1 else "Banksmartin/Basic.lean"

TOK = {
    "<<R>>":  "\u211d", "<<N>>":  "\u2115", "<<Q>>":  "\u211a",
    "<<SUM>>": "\u2211", "<<IN>>": "\u2208", "<<NIN>>": "\u2209",
    "<<LE>>": "\u2264", "<<GE>>": "\u2265", "<<NE>>": "\u2260",
    "<<LF>>": "\u230a", "<<RF>>": "\u230b", "<<POS>>": "\u208a",
    "<<S0>>": "\u2080", "<<AND>>": "\u2227", "<<TO>>": "\u2192",
    "<<ALL>>": "\u2200", "<<EX>>": "\u2203", "<<LA>>": "\u27e8",
    "<<RA>>": "\u27e9", "<<SS>>": "\u2286", "<<LARR>>": "\u2190",
    "<<AL>>": "\u03b1", "<<INV>>": "\u207b\u00b9",
}
MD5_A = "c6b1db62aef77b7387b2e80b55e3db12"
MD5_C1 = "6fc4ed0270b2d1c6bb1dbcd39f64d1b9"

PAY_A = r'''/-- Explicit-constant Ioc form of the dyadic bound, for direct use downstream
(the existential master would hide the witness after destructuring). -/
theorem sum_ratio_log_dyadic' (p<<S0>> : <<N>>) (x : <<R>>) (hp<<S0>> : 1 <<LE>> p<<S0>>) (hx : 9 <<LE>> x) :
    <<SUM>> k <<IN>> Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) <<LE>>
      384 * x * Real.log (Real.log x) / Real.log x := by
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

PAY_C1 = r'''      simp only [Nat.add_sub_cancel]
      have hxpos0 : (0:<<R>>) < x := by linarith
      rcases le_or_lt 9 x with hx9 | hx9
      · sorry -- MAINBRANCH-TODO
      · -- SMALL BRANCH: 3 <= x < 9
        rw [<<LARR>> piKFrom_succ_eq n hnpos x p<<S0>> (by linarith)]
        classical
        have hlog3_ge : (27:<<R>>)/25 <<LE>> Real.log 3 := by
          have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          have h1 : (23:<<R>>)/25 <<LE>> Real.exp (-((2:<<R>>)/25)) := by
            have := Real.add_one_le_exp (-((2:<<R>>)/25))
            linarith
          have hmul : Real.exp ((2:<<R>>)/25) * Real.exp (-((2:<<R>>)/25)) = 1 := by
            rw [<<LARR>> Real.exp_add]
            simp
          have h2 : Real.exp ((2:<<R>>)/25) <<LE>> 25/23 := by
            have hepos : (0:<<R>>) < Real.exp (-((2:<<R>>)/25)) := Real.exp_pos _
            nlinarith [hmul, h1, hepos, (Real.exp_pos ((2:<<R>>)/25)).le]
          have h4 : Real.exp ((27:<<R>>)/25) <<LE>> 3 := by
            have hsplit : Real.exp ((27:<<R>>)/25) = Real.exp 1 * Real.exp ((2:<<R>>)/25) := by
              rw [<<LARR>> Real.exp_add]
              norm_num
            rw [hsplit]
            nlinarith [he, h2, (Real.exp_pos ((2:<<R>>)/25)).le, (Real.exp_pos 1).le]
          have h5 : Real.log (Real.exp ((27:<<R>>)/25)) <<LE>> Real.log 3 :=
            Real.log_le_log (Real.exp_pos _) h4
          rwa [Real.log_exp] at h5
        have hlogx_ge : (27:<<R>>)/25 <<LE>> Real.log x :=
          le_trans hlog3_ge (Real.log_le_log (by norm_num) hx)
        have hlx_pos : (0:<<R>>) < Real.log x := by linarith
        have hlog3_le : Real.log 3 <<LE>> (9:<<R>>)/8 := by
          have he : (2.7182818283:<<R>>) < Real.exp 1 := Real.exp_one_gt_d9
          have h1 : (9:<<R>>)/8 <<LE>> Real.exp ((1:<<R>>)/8) := by
            have := Real.add_one_le_exp ((1:<<R>>)/8)
            linarith
          have h2 : (3:<<R>>) <<LE>> Real.exp ((9:<<R>>)/8) := by
            have hsplit : Real.exp ((9:<<R>>)/8) = Real.exp 1 * Real.exp ((1:<<R>>)/8) := by
              rw [<<LARR>> Real.exp_add]
              norm_num
            rw [hsplit]
            nlinarith [he, h1, (Real.exp_pos ((1:<<R>>)/8)).le, (Real.exp_pos 1).le]
          have h5 : Real.log 3 <<LE>> Real.log (Real.exp ((9:<<R>>)/8)) :=
            Real.log_le_log (by norm_num) h2
          rwa [Real.log_exp] at h5
        have hlogx_le : Real.log x <<LE>> (9:<<R>>)/4 := by
          have h1 : Real.log x <<LE>> Real.log 9 := Real.log_le_log (by linarith) (by linarith)
          have h2 : Real.log 9 = 2 * Real.log 3 := by
            rw [show (9:<<R>>) = 3 ^ 2 by norm_num, Real.log_pow]
            norm_num
          linarith [hlog3_le]
        have hLL_ge : (2:<<R>>)/27 <<LE>> Real.log (Real.log x) := by
          have h1 : Real.log ((Real.log x)<<INV>>) <<LE>> (Real.log x)<<INV>> - 1 :=
            Real.log_le_sub_one_of_pos (inv_pos.mpr hlx_pos)
          rw [Real.log_inv] at h1
          have h3 : 1 / Real.log x <<LE>> 1 / ((27:<<R>>)/25) :=
            one_div_le_one_div_of_le (by norm_num) hlogx_ge
          simp only [one_div] at h3
          have h4 : ((27:<<R>>)/25)<<INV>> = 25/27 := by norm_num
          rw [h4] at h3
          linarith [h1, h3]
        rcases Nat.lt_or_ge n 3 with hn3 | hn3
        · have hn2' : n <<LE>> 2 := by omega
          have hLLn : (4:<<R>>)/729 <<LE>> (Real.log (Real.log x)) ^ n := by
            calc (4:<<R>>)/729 = ((2:<<R>>)/27) ^ 2 := by norm_num
              _ <<LE>> ((2:<<R>>)/27) ^ n := by
                  apply pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2'
              _ <<LE>> (Real.log (Real.log x)) ^ n := by
                  apply pow_le_pow_left<<S0>> (by norm_num) hLL_ge
          have hcount : (piKFrom (n + 1) x p<<S0>> : <<R>>) <<LE>> x := by
            have h1 : piKFrom (n + 1) x p<<S0>> <<LE>> (Finset.Icc 2 <<LF>>x<<RF>><<POS>>).card := by
              unfold piKFrom
              exact Finset.card_filter_le _ _
            have h2 : (Finset.Icc 2 <<LF>>x<<RF>><<POS>>).card <<LE>> <<LF>>x<<RF>><<POS>> := by
              rw [Nat.card_Icc]
              omega
            have h3 : (<<LF>>x<<RF>><<POS>> : <<R>>) <<LE>> x := Nat.floor_le (by linarith)
            calc (piKFrom (n + 1) x p<<S0>> : <<R>>)
                <<LE>> ((Finset.Icc 2 <<LF>>x<<RF>><<POS>>).card : <<R>>) := by exact_mod_cast h1
              _ <<LE>> (<<LF>>x<<RF>><<POS>> : <<R>>) := by exact_mod_cast h2
              _ <<LE>> x := h3
          have hinv : (4:<<R>>)/9 <<LE>> 1 / Real.log x := by
            calc (4:<<R>>)/9 = 1 / ((9:<<R>>)/4) := by norm_num
              _ <<LE>> 1 / Real.log x := one_div_le_one_div_of_le hlx_pos hlogx_le
          have hs1 : (6000:<<R>>) <<LE>> (C + 1) * 2000 * x := by
            nlinarith [mul_nonneg hC.le (by linarith : (0:<<R>>) <<LE>> x)]
          have hs2 : (6000:<<R>>) * ((4:<<R>>)/729)
              <<LE>> ((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n :=
            mul_le_mul hs1 hLLn (by norm_num) (by linarith)
          have hs3 : (6000:<<R>>) * ((4:<<R>>)/729) * ((4:<<R>>)/9)
              <<LE>> (((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n) * (1 / Real.log x) :=
            mul_le_mul hs2 hinv (by norm_num) (by linarith [hs2])
          calc (piKFrom (n + 1) x p<<S0>> : <<R>>)
              <<LE>> x := hcount
            _ <<LE>> 9 := by linarith
            _ <<LE>> (6000:<<R>>) * ((4:<<R>>)/729) * ((4:<<R>>)/9) := by norm_num
            _ <<LE>> (((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n) * (1 / Real.log x) := hs3
            _ = (C + 1) * 2000 * x * (Real.log (Real.log x)) ^ n / Real.log x := by ring
        · have hzero : piKFrom (n + 1) x p<<S0>> = 0 := by
            unfold piKFrom
            apply Finset.card_eq_zero.mpr
            apply Finset.filter_eq_empty_iff.mpr
            intro m hm
            simp only [Finset.mem_Icc] at hm
            intro hcontra
            obtain <<LA>>hmO, _<<RA>> := hcontra
            have hmge : 2 ^ (n + 1) <<LE>> m := by
              have hb := pow_bigOmega_le m (by omega)
              rw [hmO] at hb
              exact hb
            have h16 : 16 <<LE>> 2 ^ (n + 1) := by
              calc (16:<<N>>) = 2 ^ 4 := by norm_num
                _ <<LE>> 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have hmle : (m:<<R>>) <<LE>> x := by
              have h1 : (m:<<R>>) <<LE>> (<<LF>>x<<RF>><<POS>> : <<R>>) := by exact_mod_cast hm.2
              have h2 : (<<LF>>x<<RF>><<POS>> : <<R>>) <<LE>> x := Nat.floor_le (by linarith)
              linarith
            have h16r : (16:<<R>>) <<LE>> (m:<<R>>) := by
              exact_mod_cast le_trans h16 hmge
            linarith
          rw [hzero]
          simp only [Nat.cast_zero]
          have hLLpos : (0:<<R>>) < Real.log (Real.log x) := Real.log_pos (by linarith)
          apply div_nonneg _ hlx_pos.le
          apply mul_nonneg _ (pow_nonneg hLLpos.le n)
          apply mul_nonneg _ (by linarith : (0:<<R>>) <<LE>> x)
          nlinarith [hC]
'''

def render(s):
    for k, v in TOK.items():
        s = s.replace(k, v)
    if "<<" in s:
        print("ERROR: unreplaced token"); sys.exit(1)
    return s

def main():
    with io.open(PATH, "r", encoding="utf-8") as fh:
        s = fh.read()
    if "sum_ratio_log_dyadic'" in s:
        print("ERROR: patch already applied; aborting."); sys.exit(1)
    a = render(PAY_A)
    c1 = render(PAY_C1)
    if hashlib.md5(a.encode()).hexdigest() != MD5_A:
        print("ERROR: PAY_A md5 mismatch - transport corruption, aborting."); sys.exit(1)
    if hashlib.md5(c1.encode()).hexdigest() != MD5_C1:
        print("ERROR: PAY_C1 md5 mismatch - transport corruption, aborting."); sys.exit(1)
    # Op 1: insert dyadic' before piKFrom_bound, docstring-aware
    i = s.find("theorem piKFrom_bound")
    if i < 0:
        print("ERROR: piKFrom_bound not found"); sys.exit(1)
    head = s[:i]
    ds = head.rfind("/--")
    if ds >= 0 and "-/" in head[ds:] and head[head.find("-/", ds) + 2:].strip() == "":
        i = ds
    s = s[:i] + a + s[i:]
    # Op 2: constant bump
    old_ref = render("      refine <<LA>>C * 100, by positivity, fun p<<S0>> x hx => ?_<<RA>>")
    new_ref = render("      refine <<LA>>(C + 1) * 2000, by nlinarith [hC], fun p<<S0>> x hx => ?_<<RA>>")
    if s.count(old_ref) != 1:
        print("ERROR: refine line - found", s.count(old_ref), "matches"); sys.exit(1)
    s = s.replace(old_ref, new_ref)
    # Op 3: sorry -> continuation
    old_sorry = "          linarith\n      sorry"
    if s.count(old_sorry) != 1:
        print("ERROR: sorry locator - found", s.count(old_sorry), "matches"); sys.exit(1)
    s = s.replace(old_sorry, "          linarith\n" + c1.rstrip("\n"))
    with io.open(PATH, "w", encoding="utf-8") as fh:
        fh.write(s)
    print("OK: all three ops applied (dyadic' + constant bump + small branch).")

if __name__ == "__main__":
    main()
PYEOF

echo "===== applying ====="
if python3 patch_dyadic7r1.py; then
  echo "===== lake build ====="
  lake build
else
  echo "PATCH FAILED - skipping build. Paste this whole output."
fi
