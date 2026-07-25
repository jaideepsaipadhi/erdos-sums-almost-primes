#!/usr/bin/env python3
import sys, io, re
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<LE>>","\u2264"),
 ("<<SUM>>","\u2211"),("<<IN>>","\u2208"),("<<RSUB>>","\u211d")]
a = io.open("payload26.txt", encoding="utf-8").read()
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a or "sorry" in a:
    print("ERROR: token or sorry check failed, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
m = re.search(r"theorem sum_pow_div_factorial_le_exp.*?positivity\n.*?exact hle\n", f, re.S)
if not m:
    m = re.search(r"theorem sum_pow_div_factorial_le_exp.*?\n\n", f, re.S)
if not m:
    print("ERROR: could not locate existing theorem"); sys.exit(1)
f = f.replace(m.group(0), a.rstrip("\n") + "\n\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: replaced with tsum-bridge version.")
