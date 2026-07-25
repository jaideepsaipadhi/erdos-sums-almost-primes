#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<LE>>","\u2264"),("<<AND>>","\u2227"),("<<NE>>","\u2260"),
 ("<<TOP>>","\u22a4"),("<<DOT>>","\u00b7"),("<<LA>>","\u27e8"),("<<RA>>","\u27e9"),
 ("<<LARR>>","\u2190")]
a = io.open("payload55.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
if "theorem gap_integrand_bounds" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- CONSEQUENCE (manuscript Thm 4.1, upper bound input)"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: gap integrand bounds + integrability installed.")
