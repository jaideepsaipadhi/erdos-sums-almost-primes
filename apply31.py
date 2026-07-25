#!/usr/bin/env python3
import sys, io, re
TOKS = [("<<R>>","\u211d"),("<<INT>>","\u222b"),("<<DOT>>","\u00b7"),
 ("<<LA>>","\u27e8"),("<<RA>>","\u27e9"),("<<FEQ>>","\u1da0")]
a = io.open("payload31.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/EulerGamma.lean", encoding="utf-8").read()
old = re.search(r"theorem hasDerivAt_EinTailFun \(a :.*?\n  sorry\n", f, re.S)
if not old:
    print("ERROR: could not locate hasDerivAt_EinTailFun"); sys.exit(1)
f = f.replace(old.group(0), a.rstrip("\n") + "\n")
io.open("Banksmartin/EulerGamma.lean", "w", encoding="utf-8").write(f)
print("OK: EinTailFun derivative installed (split lemma sorried).")
