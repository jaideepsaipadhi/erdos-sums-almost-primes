#!/usr/bin/env python3
import sys, io, re
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<DOT>>","\u00b7"),("<<UN>>","\u222a")]
a = io.open("payload33.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = re.search(r"theorem EinTailFun_split \(a :.*?\n  sorry\n", f, re.S)
if not old:
    print("ERROR: could not locate EinTailFun_split"); sys.exit(1)
f = f.replace(old.group(0), a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: EinTailFun_split installed.")
