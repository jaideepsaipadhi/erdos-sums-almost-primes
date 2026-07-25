#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<LE>>","\u2264")]
a = io.open("payload61.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """theorem gap_five_evaluation (a : \u211d) (ha : 0 < a) :
    \u222b t in Set.Ioc (0:\u211d) 1, (Real.exp (-a * t) - 1 + a * t) / t ^ 2
      \u2264 a * Real.log a + Real.eulerMascheroniConstant * a - a + 1 := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: gap_five_evaluation installed.")
