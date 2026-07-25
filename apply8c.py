#!/usr/bin/env python3
import sys, io, hashlib
TOKS = [("<<R>>","\u211d"),("<<N>>","\u2115"),("<<SUM>>","\u2211"),
 ("<<IN>>","\u2208"),("<<NIN>>","\u2209"),("<<LE>>","\u2264"),
 ("<<GE>>","\u2265"),("<<NE>>","\u2260"),("<<LF>>","\u230a"),
 ("<<RF>>","\u230b"),("<<POS>>","\u208a"),("<<S0>>","\u2080"),
 ("<<AND>>","\u2227"),("<<TO>>","\u2192"),("<<ALL>>","\u2200"),
 ("<<EX>>","\u2203"),("<<LA>>","\u27e8"),("<<RA>>","\u27e9"),
 ("<<SS>>","\u2286"),("<<LARR>>","\u2190"),("<<EMPTY>>","\u2205"),
 ("<<DOT>>","\u00b7"),("<<NOT>>","\u00ac")]
a = io.open("payload8c.txt", encoding="utf-8").read()
if hashlib.md5(a.encode()).hexdigest() != "8e7c15179043c216df18d8a7d1fd3860":
    print("ERROR: ascii md5 mismatch, aborting."); sys.exit(1)
for k, v in TOKS:
    a = a.replace(k, v)
if "<<" in a:
    print("ERROR: unreplaced token, aborting."); sys.exit(1)
if hashlib.md5(a.encode()).hexdigest() != "79301eca802722eeff829853ae9aec61":
    print("ERROR: rendered md5 mismatch, aborting."); sys.exit(1)
f = io.open("Banksmartin/Basic.lean", encoding="utf-8").read()
old = "  sorry -- partial summation against hbound; standard but not short.\n"
if f.count(old) != 1:
    print("ERROR: sorry locator - found", f.count(old), "matches; aborting."); sys.exit(1)
f = f.replace(old, a.rstrip("\n") + "\n")
io.open("Banksmartin/Basic.lean", "w", encoding="utf-8").write(f)
print("OK: fk_summable proof installed.")
