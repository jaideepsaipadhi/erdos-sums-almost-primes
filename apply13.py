#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<TO>>","\u2192"),("<<INT>>","\u222b"),
 ("<<ALL>>","\u2200"),("<<IN>>","\u2208")]
a = io.open("payload13.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: unreplaced token, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem integral_Ioc_subst" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
i = f.find("/-- DEEP FACT")
if i < 0:
    print("ERROR: anchor not found, aborting."); sys.exit(1)
f = f[:i] + a.rstrip("\n") + "\n\n" + f[i:]
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: integral_Ioc_subst installed.")
