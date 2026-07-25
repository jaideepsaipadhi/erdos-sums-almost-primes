#!/usr/bin/env python3
import sys, io
TOKS = [("<<C>>","\u2102"),("<<N>>","\u2115"),("<<NE>>","\u2260")]
a = io.open("payload75.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if "theorem deriv_geom_family_at" in f:
    print("ERROR: already applied, aborting."); sys.exit(1)
anchor = "/-- The derivative of z -> k!/(c^k (1 - z/c)^(k+1)) is the next one in the family. -/"
if f.count(anchor) != 1:
    print("ERROR: anchor count", f.count(anchor)); sys.exit(1)
f = f.replace(anchor, a.rstrip("\n") + "\n\n" + anchor)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: pointwise version installed alongside the old one.")
