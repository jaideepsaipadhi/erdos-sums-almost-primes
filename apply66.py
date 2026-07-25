#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<LE>>","\u2264"),("<<LARR>>","\u2190"),
 ("<<DOT>>","\u00b7")]
a = io.open("payload66.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = """theorem integrable_exp_Bfun (m : \u2115) :
    MeasureTheory.IntegrableOn (fun u : \u211d => Real.exp u * Bfun m u) (Set.Ioi 0) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: integrable_exp_Bfun installed.")
