#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<SUM>>","\u2211"),("<<IN>>","\u2208"),
 ("<<INT>>","\u222b"),("<<LE>>","\u2264"),("<<LARR>>","\u2190"),("<<DOT>>","\u00b7")]
a = io.open("payload65.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem sum_betaCirc_le_integral" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- DEEP FACT"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: sum_betaCirc_le_integral installed (integrability isolated).")
