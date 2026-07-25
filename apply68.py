#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<INT>>","\u222b"),("<<ALL>>","\u2200"),
 ("<<IN>>","\u2208"),("<<NE>>","\u2260"),("<<LARR>>","\u2190")]
a = io.open("payload68.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem exp_Bfun_integral_eq" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- DEEP FACT"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: exp_Bfun_integral_eq installed.")
