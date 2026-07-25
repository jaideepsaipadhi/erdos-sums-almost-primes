#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<LE>>","\u2264")]
a = io.open("payload38.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """theorem regBoundary_tendsto_zero :
    Filter.Tendsto (fun b : \u211d => (1 - Real.exp (-b)) * Real.log b)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: regBoundary_tendsto_zero installed.")
