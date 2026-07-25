#!/usr/bin/env python3
import sys, io
TOKS = [("<<C>>","\u2102"),("<<N>>","\u2115"),("<<NE>>","\u2260"),("<<DOT>>","\u00b7")]
a = io.open("payload74.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = """theorem deriv_geom_family (c : \u2102) (hc : c \u2260 0) (k : \u2115) :
    deriv (fun z : \u2102 => (Nat.factorial k : \u2102) / (c ^ k * (1 - z / c) ^ (k + 1)))
      = fun z : \u2102 => (Nat.factorial (k + 1) : \u2102) / (c ^ (k + 1) * (1 - z / c) ^ (k + 2)) := by
  sorry
"""
if f.count(old) != 1:
    print("ERROR: literal target count", f.count(old)); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: derivative computation installed (pole case isolated).")
