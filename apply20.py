#!/usr/bin/env python3
import sys, io, os
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<IN>>","\u2208"),("<<LE>>","\u2264")]
a = io.open("payload20.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: unreplaced token, aborting."); sys.exit(1)
if os.path.exists("Banksmartin/EulerGamma.lean"):
    print("ERROR: file already exists, aborting."); sys.exit(1)
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(a)
print("OK: scaffold written to Banksmartin/EulerGamma.lean (7 sorries, by design).")
