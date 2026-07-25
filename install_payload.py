#!/usr/bin/env python3
# usage: install_payload.py <payload.txt> <ascii_md5> <rendered_md5> <anchor> [<guard_name>]
import sys, io, hashlib
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<SUM>>","\u2211"),
 ("<<IN>>","\u2208"),("<<NIN>>","\u2209"),("<<LE>>","\u2264"),
 ("<<GE>>","\u2265"),("<<NE>>","\u2260"),("<<LF>>","\u230a"),
 ("<<RF>>","\u230b"),("<<POS>>","\u208a"),("<<S0>>","\u2080"),
 ("<<AND>>","\u2227"),("<<TO>>","\u2192"),("<<ALL>>","\u2200"),
 ("<<EX>>","\u2203"),("<<LA>>","\u27e8"),("<<RA>>","\u27e9"),
 ("<<SS>>","\u2286"),("<<LARR>>","\u2190"),("<<EMPTY>>","\u2205"),
 ("<<DOT>>","\u00b7")]
pay, amd5, rmd5, anchor = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
guard = sys.argv[5] if len(sys.argv) > 5 else None
a = io.open(pay, encoding="utf-8").read()
if hashlib.md5(a.encode()).hexdigest() != amd5:
    print("ERROR: ascii payload md5 mismatch - transcription corrupt, aborting."); sys.exit(1)
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: unreplaced token; aborting."); sys.exit(1)
if hashlib.md5(a.encode()).hexdigest() != rmd5:
    print("ERROR: rendered md5 mismatch; aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
if guard and guard in f:
    print("ERROR: already applied (guard hit); aborting."); sys.exit(1)
i = f.find(anchor)
if i < 0:
    print("ERROR: anchor not found; aborting."); sys.exit(1)
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(
    f[:i] + a.rstrip("\n") + "\n\n" + f[i:])
print("OK: payload installed before anchor.")
