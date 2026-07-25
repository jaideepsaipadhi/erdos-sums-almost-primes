#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b")]
a = io.open("payload44.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """      have hcalc : (\u222b v in Set.Ioc (0:\u211d) b, 4 * v ^ (-(1:\u211d)/4))
          = (16/3) * b ^ ((3:\u211d)/4) := by
        sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: hcalc installed.")
