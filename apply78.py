#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<C>>","\u2102"),("<<N>>","\u2115"),("<<NE>>","\u2260")]
a = io.open("payload78.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = """theorem coeff_pow_neg (s : \u211d) (hs : 1 < s) (l : \u2115) :
    (iteratedDeriv l (fun z : \u2102 => ((s - 1 : \u211d) : \u2102) ^ (-z)) 0)
        / (Nat.factorial l : \u2102)
      = ((-Real.log (s - 1)) ^ l / (Nat.factorial l) : \u211d) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: coeff_pow_neg installed.")
