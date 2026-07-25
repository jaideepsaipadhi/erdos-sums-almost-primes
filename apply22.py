#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<UN>>","\u222a"),("<<LARR>>","\u2190")]
a = io.open("payload22.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """theorem gammaDeriv_dom_integrable :
    IntegrableOn gammaDeriv_dom (Set.Ioi 0) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: Obligation 1 closed via union.")
