#!/usr/bin/env python3
"""Combine fodd chunks, add the tail balls, report enclosures + monotonicity.

The odd analogue of numerics/combine.py.  fodd_run.py with a panel range
writes ochunks/oP0_P1.txt holding the partial f_k as midpoint and radius; this
sums them, checks the panels cover [0, NPANEL) with no gap and no overlap,
adds tail_large_s_odd and tail_near_1 once, and prints the same report the
monolithic run prints.

Usage: python3 fodd_combine.py [KMAX] [PREC]
"""
import glob, sys
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 75
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
sys.argv = ["x", str(KMAX), str(PREC)]
from flint import arb, ctx
sys.path.insert(0, "../../numerics")
import certified as C
import fodd_run as F

ctx.prec = PREC
files = sorted(glob.glob("ochunks/o*.txt"))
spans = [tuple(map(int, f.split('/o')[1].split('.')[0].split('_'))) for f in files]
cov = 0
for a, b in sorted(spans):
    assert a == cov, "gap or overlap at panel %d (chunk starts at %d)" % (cov, a)
    cov = b
assert cov == C.NPANEL, "coverage ends at %d, need %d" % (cov, C.NPANEL)
print("# %d chunks cover panels 0..%d with no gap" % (len(files), cov))

fk = [arb(0)] * (KMAX + 1)
for f in files:
    for line in open(f):
        if line.startswith("#"):
            continue
        p = line.split()
        k = int(p[0])
        mid, rad = arb(p[1]), arb(p[2])
        fk[k] += mid.union(mid - rad).union(mid + rad)

# From k = 1, not k = 2.  This loop used to start at 2, so f_1 carried no
# tail terms and the verdict below never compared f_1 with f_2 -- the sweep
# certified [2,75] while the manuscript claims 1 <= k <= 75.  (The tails at
# k = 1 are ~3e-79 against a radius of ~3e-22, so nothing was false; it was
# simply unverified.)
for k in range(1, KMAX + 1):
    fk[k] += F.tail_large_s_odd(k) + C.tail_near_1(k)

print("k   f_k^odd")
for k in range(1, KMAX + 1):
    print("%2d  %s" % (k, fk[k].str(20)), flush=True)
print()
# range(1, KMAX) compares every adjacent pair (k, k+1) for 1 <= k <= KMAX-1.
# So with KMAX = 75 the comparison is certified for 1 <= k <= 74, NOT 1 <= k
# <= 75: the pair (75, 76) would need g_76, which is not computed.  The
# enclosures cover [1, KMAX]; the monotonicity verdict covers [1, KMAX-1].
# The paper states both ranges separately for this reason.
dec = all((fk[k] - fk[k + 1]) > 0 for k in range(1, KMAX))
print("f_k^odd strictly decreasing on [1,%d]: %s" % (KMAX - 1, dec))
inc = all((fk[k + 1] - fk[k]) > 0 for k in range(1, KMAX))
print("f_k^odd strictly increasing on [1,%d]: %s" % (KMAX - 1, inc))
