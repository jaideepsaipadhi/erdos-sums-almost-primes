#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<C>>","\u2102"),("<<N>>","\u2115"),("<<LE>>","\u2264"),
 ("<<SUM>>","\u2211"),("<<IN>>","\u2208"),("<<LARR>>","\u2190")]
a = io.open("payload81.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = """theorem Fk_expansion (k : \u2115) (s : \u211d) (hs : 1 < s) (hs2 : s \u2264 2) :
    Fk k s = \u2211 p \u2208 Finset.range (k + 1),
      \u2211 q \u2208 Finset.range (k - p + 1),
        (gCoeff q s).re * (2:\u211d) ^ (-((p:\u211d)) * s)
          * ((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q))) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: Fk_expansion chained from L2a + L2b.")
