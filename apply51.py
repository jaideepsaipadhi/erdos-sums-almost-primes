#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<LE>>","\u2264"),("<<INT>>","\u222b"),
 ("<<ALL>>","\u2200"),("<<TO>>","\u2192"),("<<ALLF>>","\u2200\u1da0"),("<<LARR>>","\u2190")]
a = io.open("payload51.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """theorem ein_eq (a : \u211d) (ha : 0 < a) :
    Ein a = Real.eulerMascheroniConstant + Real.log a + EinTailFun a := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: ein_eq installed.")
