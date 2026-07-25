#!/usr/bin/env python3
import sys, io
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<IN>>","\u2208"),("<<FEQ>>","\u1da0")]
a = io.open("payload24.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
import re
old4 = re.search(r"theorem hasDerivAt_Gamma \(s :.*?\n  sorry\n", f, re.S)
oldT = re.search(r"theorem eulerMascheroni_eq_integral :.*?\n  sorry\n", f, re.S)
if not old4 or not oldT:
    print("ERROR: could not locate one of the targets"); sys.exit(1)
parts = a.split("\ntheorem eulerMascheroni_eq_integral")
if len(parts) != 2:
    print("ERROR: payload split failed"); sys.exit(1)
f = f.replace(old4.group(0), parts[0].rstrip("\n") + "\n")
f = f.replace(oldT.group(0), "theorem eulerMascheroni_eq_integral" + parts[1].rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: Obligation 4 and Target installed.")
