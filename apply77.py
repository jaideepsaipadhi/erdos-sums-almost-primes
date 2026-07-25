#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<C>>","\u2102"),("<<N>>","\u2115"),("<<NE>>","\u2260"),
 ("<<LE>>","\u2264"),("<<INV>>","\u207b\u00b9"),("<<LARR>>","\u2190")]
a = io.open("payload77.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = """theorem coeff_geom (s : \u211d) (hs : 1 < s) (j : \u2115) :
    (iteratedDeriv j (fun z : \u2102 => (1 - z / ((2:\u2102) ^ (s:\u2102)))\u207b\u00b9) 0)
        / (Nat.factorial j : \u2102)
      = ((2:\u211d) ^ (-(j:\u211d) * s) : \u211d) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: coeff_geom installed.")
