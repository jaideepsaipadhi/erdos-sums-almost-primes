#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<LE>>","\u2264"),("<<ALL>>","\u2200"),
 ("<<IN>>","\u2208"),("<<DOT>>","\u00b7"),("<<INV>>","\u207b\u00b9")]
a = io.open("payload37.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
if "theorem hasDerivAt_regAntideriv" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- STEP C: Ein(a) = gamma + log a + tail(a)."
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: regularized by-parts installed.")
