#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<DOT>>","\u00b7"),("<<LA>>","\u27e8"),("<<RA>>","\u27e9")]
a = io.open("payload67.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem expNeg_image" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- DEEP FACT"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: expNeg image + injectivity installed.")
