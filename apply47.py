#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<LE>>","\u2264"),("<<INT>>","\u222b"),
 ("<<DOT>>","\u00b7"),("<<S0>>","\u2080")]
a = io.open("payload47.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = """theorem expNeg_log_tendsto_zero :
    Filter.Tendsto (fun n : \u2115 => Real.exp (-(n:\u211d)) * Real.log (n:\u211d))
      Filter.atTop (nhds 0) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: expNeg_log_tendsto_zero installed.")
