#!/usr/bin/env python3
import sys, io, hashlib
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<SUM>>","\u2211"),("<<IN>>","\u2208"),
 ("<<ALL>>","\u2200"),("<<INT>>","\u222b"),("<<PD>>","\u2202")]
a = io.open("payload10.txt", encoding="utf-8").read()
if hashlib.md5(a.encode()).hexdigest() != "bd8bf727a8061d24735a9408ba5c3d1f":
    print("ERROR: ascii md5 mismatch, aborting."); sys.exit(1)
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or hashlib.md5(a.encode()).hexdigest() != "f9dd83cfa2a22ad2d5ac8d130281d24c":
    print("ERROR: render check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "noncomputable def Sm" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
i = f.find("/-- DEEP FACT")
if i < 0:
    print("ERROR: anchor not found, aborting."); sys.exit(1)
f = f[:i] + a.rstrip("\n") + "\n\n" + f[i:]
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: Definition 2.3 objects installed (Sm, Am, deltaM + anchors).")
