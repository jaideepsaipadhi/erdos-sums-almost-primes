#!/usr/bin/env python3
import sys, io, re
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<LE>>","\u2264"),
 ("<<DOT>>","\u00b7"),("<<FEQ>>","\u1da0")]
a = io.open("payload30.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = re.search(r"theorem hasDerivAt_Ein \(a :.*?\n  sorry\n", f, re.S)
if not old:
    print("ERROR: could not locate hasDerivAt_Ein"); sys.exit(1)
f = f.replace(old.group(0), a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: Ein FTC derivative installed.")
