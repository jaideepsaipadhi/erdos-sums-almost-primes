#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<LE>>","\u2264"),("<<UN>>","\u222a"),
 ("<<ALL>>","\u2200"),("<<IN>>","\u2208"),("<<LA>>","\u27e8"),("<<RA>>","\u27e9"),
 ("<<LARR>>","\u2190"),("<<FEQ>>","\u1da0")]
a = io.open("payload42.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """theorem euler_parts_limit (c : \u211d) (hc : 0 < c) :
    (\u222b v in Set.Ioc (0:\u211d) c, Real.exp (-v) * Real.log v) + Ein c
      = (1 - Real.exp (-c)) * Real.log c := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: euler_parts_limit installed with one internal sorry (h3).")
