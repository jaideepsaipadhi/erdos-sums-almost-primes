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
}

NEW = r'''
/-- Decompose a sum over `Ioc p<<S0>> N` into dyadic fibers indexed by `Nat.log 2 k`.
Pure bookkeeping via `Finset.sum_fiberwise_of_maps_to`: fibers of a function are
disjoint for free, so no partition or covering lemma is needed. -/
theorem sum_dyadic_fiberwise (p<<S0>> N : <<N>>) (g : <<N>> <<TO>> <<R>>) :
    <<SUM>> k <<IN>> Finset.Ioc p<<S0>> N, g k =
      <<SUM>> j <<IN>> Finset.range (Nat.log 2 N + 1),
        <<SUM>> k <<IN>> (Finset.Ioc p<<S0>> N).filter (fun k => Nat.log 2 k = j), g k := by
  classical
  refine (Finset.sum_fiberwise_of_maps_to ?_ g).symm
  intro k hk
  simp only [Finset.mem_Ioc] at hk
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.log_mono_right hk.2

/-- Elements of dyadic fiber `j` satisfy `2^j <<LE>> k < 2^(j+1)`. -/
theorem dyadic_fiber_mem_bounds (p<<S0>> N j k : <<N>>)
    (hk : k <<IN>> (Finset.Ioc p<<S0>> N).filter (fun k => Nat.log 2 k = j)) :
    2 ^ j <<LE>> k <<AND>> k < 2 ^ (j + 1) := by
  classical
  obtain <<LA>>hkmem, hkj<<RA>> := Finset.mem_filter.mp hk
  simp only [Finset.mem_Ioc] at hkmem
  have hk0 : k <<NE>> 0 := by omega
  constructor
  · calc 2 ^ j = 2 ^ Nat.log 2 k := by rw [hkj]
      _ <<LE>> k := Nat.pow_log_le_self 2 hk0
  · calc k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
      _ = 2 ^ (j + 1) := by rw [hkj]

/-- The number of primes in dyadic fiber `j` is at most pi(2^(j+1)). -/
theorem dyadic_fiber_prime_card (p<<S0>> N j : <<N>>) :
    ((((Finset.Ioc p<<S0>> N).filter (fun k => Nat.log 2 k = j)).filter
        (fun k => Nat.Prime k)).card : <<R>>) <<LE>>
      (Nat.primeCounting (2 ^ (j + 1)) : <<R>>) := by
  classical
  have hsub : (((Finset.Ioc p<<S0>> N).filter (fun k => Nat.log 2 k = j)).filter
      (fun k => Nat.Prime k)) <<SS>>
      (Finset.range (2 ^ (j + 1) + 1)).filter Nat.Prime := by
    intro k hk
    obtain <<LA>>hkfib, hkp<<RA>> := Finset.mem_filter.mp hk
    have hb := dyadic_fiber_mem_bounds p<<S0>> N j k hkfib
    refine Finset.mem_filter.mpr <<LA>>?_, hkp<<RA>>
    exact Finset.mem_range.mpr (by omega)
  have hcount : Nat.primeCounting (2 ^ (j + 1)) =
      ((Finset.range (2 ^ (j + 1) + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hcard := Finset.card_le_card hsub
  rw [hcount]
  exact_mod_cast hcard

/-- h(t) = (x/t)/log(x/t) is antitone on [1, x/3]. Extracted from the argument
inside `h_p0_bound` so it can be reused per dyadic fiber. -/
theorem ratio_log_antitoneOn (x : <<R>>) (hx : 3 <<LE>> x) :
    AntitoneOn (fun s => (x / s) / Real.log (x / s)) (Set.Icc (1:<<R>>) (x / 3)) := by
  have hxpos : (0:<<R>>) < x := by linarith
  have hconv : Convex <<R>> (Set.Icc (1:<<R>>) (x/3)) := convex_Icc _ _
  have hint_eq : interior (Set.Icc (1:<<R>>) (x/3)) = Set.Ioo (1:<<R>>) (x/3) := interior_Icc
  have hxt3_of : <<ALL>> t, 1 <<LE>> t <<TO>> t <<LE>> x/3 <<TO>> (3:<<R>>) <<LE>> x / t := by
    intro t ht1 ht2
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have heq3 : x / (x/3) = 3 := by field_simp
    have hge : x / (x/3) <<LE>> x / t := div_le_div_of_nonneg_left hxpos.le htpos ht2
    linarith [heq3 \u25b8 hge]
  have hcont : ContinuousOn (fun s => (x/s)/Real.log (x/s)) (Set.Icc (1:<<R>>) (x/3)) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht.1
    have hxt3 := hxt3_of t ht.1 ht.2
    exact (differentiableAt_ratio_log x t htpos (by linarith)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn <<R>> (fun s => (x/s)/Real.log (x/s))
      (interior (Set.Icc (1:<<R>>) (x/3))) := by
    rw [hint_eq]
    intro t ht
    simp only [Set.mem_Ioo] at ht
    have htpos : 0 < t := lt_trans one_pos ht.1
    have hxt3 := hxt3_of t ht.1.le ht.2.le
    exact (differentiableAt_ratio_log x t htpos (by linarith)).differentiableWithinAt
  have hderiv_np : <<ALL>> t <<IN>> interior (Set.Icc (1:<<R>>) (x/3)),
      deriv (fun s => (x/s)/Real.log (x/s)) t <<LE>> 0 := by
    rw [hint_eq]
    intro t ht
    simp only [Set.mem_Ioo] at ht
    have htpos : 0 < t := lt_trans one_pos ht.1
    have hxt3 := hxt3_of t ht.1.le ht.2.le
    have hxt : 1 < x / t := by linarith
    rw [deriv_ratio_log_eq x t htpos hxt]
    have hlogxt_gt1 : 1 < Real.log (x/t) := by
      have h3le : Real.log 3 <<LE>> Real.log (x/t) := Real.log_le_log (by norm_num) hxt3
      have hloge1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have hl3 : (1:<<R>>) < Real.log 3 := by
        calc (1:<<R>>) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hloge1
      linarith
    have hnum_neg : (1:<<R>>) - Real.log (x/t) < 0 := by linarith
    have hden_pos : (0:<<R>>) < (Real.log (x/t))^2 := by positivity
    have hxt2_pos : (0:<<R>>) < x/t^2 := by positivity
    have hprod_neg : x/t^2 * (1 - Real.log (x/t)) < 0 :=
      mul_neg_of_pos_of_neg hxt2_pos hnum_neg
    exact div_nonpos_of_nonpos_of_nonneg hprod_neg.le hden_pos.le
  exact antitoneOn_of_deriv_nonpos hconv hcont hdiff hderiv_np

/-- THE dyadic sum bound (statement only for now): the weighted prime sum
<<SUM>>_(p prime <<LE>> x/3) (x/p)/log(x/p) is O(x loglog x / log x). This is the
last analytic wall of piKFrom_bound's inductive step. -/
theorem sum_ratio_log_dyadic :
    <<EX>> K : <<R>>, 0 < K <<AND>> <<ALL>> (p<<S0>> : <<N>>) (x : <<R>>), 1 <<LE>> p<<S0>> <<TO>> 9 <<LE>> x <<TO>>
      <<SUM>> k <<IN>> Finset.Ioc p<<S0>> <<LF>>x / 3<<RF>><<POS>>,
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : <<R>>) <<LE>>
        K * x * Real.log (Real.log x) / Real.log x := by
  sorry

'''

def main():
    with io.open(PATH, "r", encoding="utf-8") as fh:
        s = fh.read()
    start_marker = "theorem dyadic_partition_scaffold"
    end_marker = "theorem sum_ratio_log_bound_gen"
    i = s.find(start_marker)
    if i < 0:
        print("ERROR: scaffold not found; aborting, file untouched."); sys.exit(1)
    if s.find(start_marker, i + 1) >= 0:
        print("ERROR: scaffold marker appears twice; aborting."); sys.exit(1)
    head = s[:i]
    ds = head.rfind("/--")
    if ds >= 0 and "-/" in head[ds:] and head[head.find("-/", ds) + 2:].strip() == "":
        i = ds
    j = s.find(end_marker, i)
    if j < 0:
        print("ERROR: sum_ratio_log_bound_gen not found after scaffold; aborting."); sys.exit(1)
    new = NEW
    for k, v in TOK.items():
        new = new.replace(k, v)
    new = new.replace("\\u25b8", "\u25b8")
    if "<<" in new:
        print("ERROR: unreplaced token remains; aborting."); sys.exit(1)
    out = s[:i] + new.lstrip("\n") + s[j:]
    with io.open(PATH, "w", encoding="utf-8") as fh:
        fh.write(out)
    print("OK: scaffold replaced.")
    for name in ["sum_dyadic_fiberwise", "dyadic_fiber_mem_bounds",
                 "dyadic_fiber_prime_card", "ratio_log_antitoneOn",
                 "sum_ratio_log_dyadic"]:
        print("  ", name, "present:", ("theorem " + name) in out)

if __name__ == "__main__":
    main()
