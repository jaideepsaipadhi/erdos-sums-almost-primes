#!/usr/bin/env python3
import sys, io
TOKS = [("<<C>>","\u2102"),("<<N>>","\u2115"),("<<LE>>","\u2264"),("<<NE>>","\u2260"),
 ("<<LARR>>","\u2190")]
a = io.open("payload87.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem choose_mul_choose_div_factorial" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- OBLIGATION L2b: the k-th coefficient of Fbig is the triple convolution"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: trinomial identity installed.")
