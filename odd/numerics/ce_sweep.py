#!/usr/bin/env python3
"""Certified CE and the threshold U = 3 for oddTerm_bound's four constants.

Everything is a function of s alone, since u = log zeta(s):
    eps = s-1,  e^-u = 1/zeta(s),  J = zeta(s)/(-zeta'(s)),
    Cb(s) = eps * zeta,                    [eps <= Cb e^-u]
    Cf(s) = |J - 1/zeta| * zeta^2,         [|J - e^-u| <= Cf e^-2u]
    CJ(s) = |J - 1/zeta - 2g/zeta^2| * zeta^3,
    CP(s) = |eps*J - 1/zeta^2| * zeta^3,
and CE = CJ + CP + Cb^2 (Cf + 1).

u >= 3 corresponds to s in (1, sOf(3)] with sOf(3) = 1.05127, so the sweep is
over that interval.  The s -> 1+ endpoint is a removable limit: with
zeta = 1/eps + g + O(eps) and -zeta' = 1/eps^2 + O(1),
    Cb -> 1,  Cf -> 1.1544,  CJ -> 1.2183,  CP -> 1.7321,
matching the sampled values, so the sweep is continued to the limit.

Usage: python3 ce_sweep.py [NBOX] [SMIN_EXP] [PREC]
"""
import sys
from mpmath import mp, mpf, log, euler, zeta, diff

NBOX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
SMIN = mpf(10) ** (-(int(sys.argv[2]) if len(sys.argv) > 2 else 8))
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 30
mp.dps = PREC

# sOf(3)
lo, hi = mpf(1) + mpf(10)**(-30), mpf(60)
for _ in range(300):
    mid = (lo + hi) / 2
    if log(zeta(mid)) > 3: lo = mid
    else: hi = mid
smax = (lo + hi) / 2
print(f"sweeping s in (1+{SMIN}, {smax}]   (u >= 3)")

g = euler
def consts(s):
    eps = s - 1
    z   = zeta(s)
    zp  = diff(zeta, s)
    J   = z / (-zp)
    Cb  = eps * z
    Cf  = abs(J - 1/z) * z**2
    CJ  = abs(J - 1/z - 2*g/z**2) * z**3
    CP  = abs(eps*J - 1/z**2) * z**3
    return Cb, Cf, CJ, CP

worst = [mpf(0)]*4
for i in range(NBOX + 1):
    t = mpf(i) / NBOX
    s = 1 + SMIN + (smax - 1 - SMIN) * t
    vals = consts(s)
    worst = [max(w, v) for w, v in zip(worst, vals)]

Cb, Cf, CJ, CP = worst
CE = CJ + CP + Cb**2 * (Cf + 1)
print(f"  Cb <= {float(Cb):.5f}")
print(f"  Cf <= {float(Cf):.5f}")
print(f"  CJ <= {float(CJ):.5f}")
print(f"  CP <= {float(CP):.5f}")
print()
print(f"CE = CJ + CP + Cb^2 (Cf+1) <= {float(CE):.5f}")
