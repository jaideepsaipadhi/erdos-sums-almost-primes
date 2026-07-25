#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<C>>","\u2102"),("<<N>>","\u2115"),("<<LE>>","\u2264"),
 ("<<INV>>","\u207b\u00b9"),("<<SUM>>","\u2211"),("<<IN>>","\u2208")]
a = io.open("payload80.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "def Fbig" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- OBLIGATION L2: F_k(s) is the k-th Taylor coefficient of Fgen in z. -/"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: L2 restated as L2a + L2b.")
