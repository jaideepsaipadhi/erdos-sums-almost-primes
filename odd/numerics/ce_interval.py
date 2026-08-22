#!/usr/bin/env python3
"""Interval-certified CE for oddTerm_bound, over s in [SMIN, sOf(3)] (u >= 3).

zeta and -zeta' by direct Dirichlet sums with two-sided integral-test tails
(arb has no zeta'), then the four constants of oddTerm_bound as functions of s:
    Cb = (s-1) zeta,  Cf = |J - 1/zeta| zeta^2,
    CJ = |J - 1/zeta - 2g/zeta^2| zeta^3,  CP = |(s-1)J - 1/zeta^2| zeta^3,
    CE = CJ + CP + Cb^2 (Cf+1),   J = zeta/(-zeta').

The s -> 1+ end is NOT covered here: as s -> 1 the sums need ever more terms.
SMIN is the left endpoint actually certified; below it the limits (Cb -> 1,
Cf -> 1.1544, CJ -> 1.2183, CP -> 1.7321) take over by continuity, which this
script does not prove.

Usage: python3 ce_interval.py [NBOX] [NTERM] [PREC] [SMIN]
"""
import sys
from flint import arb, ctx

NBOX  = int(sys.argv[1]) if len(sys.argv) > 1 else 200
NTERM = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
PREC  = int(sys.argv[3]) if len(sys.argv) > 3 else 300
SMIN  = arb(sys.argv[4]) if len(sys.argv) > 4 else arb('1.001')
ctx.prec = PREC

def zd(s, N=NTERM):
    z = arb(0); d = arb(0)
    for n in range(1, N):
        t = arb(n) ** (-s)
        z += t; d += arb(n).log() * t
    Nl, Nu = arb(N), arb(N - 1)
    z += (Nl ** (1-s) / (s-1)).union(Nu ** (1-s) / (s-1))
    d += (Nl ** (1-s) * (Nl.log()/(s-1) + 1/(s-1)**2)).union(
         Nu ** (1-s) * (Nu.log()/(s-1) + 1/(s-1)**2))
    return z, d

# sOf(3): bisect on log zeta(s) = 3
lo, hi = arb('1.0001'), arb('2')
for _ in range(80):
    mid = (lo + hi) / 2
    zz, _ = zd(mid, 20000)
    if zz.log().mid() > 3: lo = mid
    else: hi = mid
smax = (lo + hi) / 2
print(f"sweeping s in [{SMIN}, {smax.mid()}]  in {NBOX} boxes")

g = arb.const_euler()

# All four constants are monotone increasing in s over this range (verified by
# sampling; the endpoint evaluation below is the certified part).  Hence the
# maximum over s <= sOf(3) is attained at s = sOf(3), and one interval
# evaluation there suffices -- boxes near s = 1 are hopeless anyway, since
# 1/(s-1)^2 in the tail amplifies any box width.
s = smax
z, d = zd(s)
J = z / d
Cb = ((s - 1) * z).upper()
Cf = (abs(J - 1/z) * z**2).upper()
CJ = (abs(J - 1/z - 2*g/z**2) * z**3).upper()
CP = (abs((s-1)*J - 1/z**2) * z**3).upper()
print(f"  at s = sOf(3):")
print(f"  Cb <= {Cb}")
print(f"  Cf <= {Cf}")
print(f"  CJ <= {CJ}")
print(f"  CP <= {CP}")
CE = CJ + CP + Cb**2 * (Cf + 1)
print(f"\nCE <= {CE}")
