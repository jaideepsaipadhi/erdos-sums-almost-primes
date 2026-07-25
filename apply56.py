#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<LE>>","\u2264"),("<<UN>>","\u222a"),
 ("<<ALL>>","\u2200"),("<<IN>>","\u2208"),("<<LA>>","\u27e8"),("<<RA>>","\u27e9"),
 ("<<LARR>>","\u2190"),("<<FEQ>>","\u1da0"),("<<ALLF>>","\u2200\u1da0")]
a = io.open("payload56.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
if "theorem gap_parts_limit" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- CONSEQUENCE (manuscript Thm 4.1, upper bound input)"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: gap_parts_limit installed (hg2 isolated).")
