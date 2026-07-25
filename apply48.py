#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<ALL>>","\u2200"),("<<IN>>","\u2208")]
a = io.open("payload48.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
if "theorem integral_Ioi_exp_neg" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- The tail integral vanishes at infinity. -/"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: integral_Ioi_exp_neg installed (one internal sorry).")
