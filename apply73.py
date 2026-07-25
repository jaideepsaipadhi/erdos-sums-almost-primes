#!/usr/bin/env python3
import sys, io
TOKS = [("<<C>>","\u2102"),("<<N>>","\u2115"),("<<NE>>","\u2260"),("<<INV>>","\u207b\u00b9"),
 ("<<ALL>>","\u2200"),("<<TO>>","\u2192")]
a = io.open("payload73.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: token check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem iteratedDeriv_geom" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-!\n## Manuscript Lemma 2.2"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: geom family installed (derivative step isolated).")
