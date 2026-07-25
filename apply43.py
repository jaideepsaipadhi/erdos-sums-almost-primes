#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<LE>>","\u2264"),("<<IN>>","\u2208"),
 ("<<DOT>>","\u00b7"),("<<ALLF>>","\u2200\u1da0")]
a = io.open("payload43.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """    have h3 : Filter.Tendsto
        (fun b : \u211d => \u222b v in Set.Ioc (0:\u211d) b, Real.exp (-v) * Real.log v)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: h3 installed with one internal sorry (hcalc).")
