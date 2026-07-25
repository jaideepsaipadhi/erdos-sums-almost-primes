#!/usr/bin/env python3
import sys, io, hashlib
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<PROD>>","\u220f"),("<<INV>>","\u207b\u00b9")]
a = io.open("payload9.txt", encoding="utf-8").read()
if hashlib.md5(a.encode()).hexdigest() != "96cb98b0cfa0fd193686b37223da9192":
    print("ERROR: ascii md5 mismatch, aborting."); sys.exit(1)
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or hashlib.md5(a.encode()).hexdigest() != "81a0d3f6dfae82b42f9c0334bfc1ae07":
    print("ERROR: render check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = "noncomputable def dConst : \u211d := 0.3786950\n"
if f.count(old) != 1:
    print("ERROR: dConst locator - found", f.count(old), "matches; aborting."); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: dConst is now the genuine Euler product; aOneConst added.")
