#!/usr/bin/env python3
import sys, io, re
TOKS = [("<<R>>","\u211d"),("<<TO>>","\u2192")]
a = io.open("payload32.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = re.search(r"theorem einCombo_const \(a b :.*?\n  sorry\n", f, re.S)
if not old:
    print("ERROR: could not locate einCombo_const"); sys.exit(1)
f = f.replace(old.group(0), a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: einCombo_const installed.")
