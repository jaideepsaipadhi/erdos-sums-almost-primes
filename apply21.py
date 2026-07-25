#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<LE>>","\u2264"),("<<SS>>","\u2286"),
 ("<<DOT>>","\u00b7"),("<<LARR>>","\u2190")]
a = io.open("payload21.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
if "gammaDeriv_dom_integrableOn_Ici" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- OBLIGATION 1: the dominating function is integrable on (0, infty). -/"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: tail half installed.")
