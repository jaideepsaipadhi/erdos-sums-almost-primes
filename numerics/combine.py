"""Combine certified chunks, add tail balls, report enclosures + monotonicity."""
from flint import arb, ctx
import glob, sys
sys.argv = ['x', '20', '300']
import certified as C
ctx.prec = 300
KMAX = 20
fk=[arb(0)]*(KMAX+1); fks=[arb(0)]*(KMAX+1)
files = sorted(glob.glob("cchunks/c*.txt"))
# verify full coverage
spans = [tuple(map(int, f.split('/c')[1].split('.')[0].split('_'))) for f in files]
cov = 0
for a,b in spans:
    assert a == cov, f"gap before panel {a}"
    cov = b
assert cov == C.NPANEL, f"coverage ends at {cov}, need {C.NPANEL}"
for f in files:
    for line in open(f):
        p = line.split()
        k = int(p[0])
        fk[k]  += arb(p[1]) + arb(0).union(arb(p[2]).union(-arb(p[2])))
        fks[k] += arb(p[3]) + arb(0).union(arb(p[4]).union(-arb(p[4])))
for k in range(2, KMAX+1):
    t = C.tail_large_s(k) + C.tail_near_1(k)
    fk[k] += t; fks[k] += t
    print(k, fk[k].str(30), fks[k].str(30))
mono  = all(bool((fk[k+1]-fk[k]) > 0) for k in range(6, KMAX))
monos = all(bool((fks[k]-fks[k+1]) > 0) for k in range(2, KMAX))
print(f"# CERTIFIED f_k strictly increasing on [6,{KMAX}]: {mono}")
print(f"# CERTIFIED f*_k strictly decreasing on [2,{KMAX}]: {monos}")
print("# max radius:", max(float(fk[k].rad()) for k in range(2,KMAX+1)))
