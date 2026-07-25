#!/usr/bin/env python3
import sys, io, re
TOKS = [("<<C>>","\u2102"),("<<N>>","\u2115"),("<<NE>>","\u2260"),("<<INV>>","\u207b\u00b9"),
 ("<<ALL>>","\u2200"),("<<IN>>","\u2208"),("<<ALLF>>","\u2200\u1da0")]
a = io.open("payload76.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
start = f.find("/-- The derivative of z -> k!/(c^k (1 - z/c)^(k+1)) is the next one in the family. -/")
if start < 0:
    print("ERROR: old family docstring not found"); sys.exit(1)
endmark = "  rw [hfam n]\n  simp\n"
end = f.find(endmark, start)
if end < 0:
    print("ERROR: end of old iteratedDeriv_geom not found"); sys.exit(1)
end += len(endmark)
f = f[:start] + a.rstrip("\n") + "\n" + f[end:]
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: old global family + old iteratedDeriv_geom replaced.")
