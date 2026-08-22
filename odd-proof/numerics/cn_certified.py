#!/usr/bin/env python3
"""Interval-certified CN with FkOdd k (sOf 3) <= CN 3^-k for all k.

FkOdd k s = sum over odd n with Omega(n) = k of n^-s, whose generating function
is the odd Euler product prod_{p>=3} (1 - z p^-s)^-1.  With L_j = P_odd(js)/j
the coefficients follow from F_0 = 1, F_k = (1/k) sum_{j<=k} j L_j F_{k-j}.

The prime sums are evaluated by the Moebius series for the prime zeta function,

    P(t) = sum_{n>=1} mu(n)/n * log zeta(nt),      P_odd(t) = P(t) - 2^-t,

which arb computes to full precision.  This replaces enumerating primes to a
cutoff and bounding the remainder: at s = sOf(3) ~ 1.05 that tail converges so
slowly that even PCUT = 1e8 with Rosser-Schoenfeld leaves a 2x over-bound, and
compounding it through 200 recurrence steps inflated CN from 364 to 3820 --
enough to push K0 past the certified sweep.

s = sOf(3) is enclosed by arb bisection with a proved bracket
log zeta(s_lo) > 3 > log zeta(s_hi); every quantity here decreases in s, so
evaluating at s_lo bounds the whole bracket.

HEAD k <= KMAX by the recursion; TAIL k > KMAX by Cauchy on |z| = R < 3^s,
FkOdd_k <= M_R R^-k with M_R = prod_{p>=3} (1 - R p^-s)^-1, whose logarithm is
sum_{m>=1} R^m P_odd(ms)/m -- again by the Moebius series.

PRECISION.  The recurrence loses about one digit every 2.3 steps to
cancellation, so 300 bits is exhausted near k = 200 (the radius reaches 3e+03
and the midpoint goes negative).  600 bits is ample: the radius at k = 200 is
1e-87, and 1200 bits gives the identical head to every printed digit.

Usage: python3 cn_certified.py [KMAX] [NMOB] [PREC]
"""
import sys
from flint import arb, ctx
from sympy import mobius

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
NMOB = int(sys.argv[2]) if len(sys.argv) > 2 else 100
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 600
ctx.prec = PREC
one, three = arb(1), arb(3)

# --- s = sOf(3) with a proved bracket ---------------------------------------
lo, hi = arb('1.05'), arb('1.06')
assert (lo.zeta().log() > three) == True and (hi.zeta().log() < three) == True
for _ in range(80):
    mid = (lo + hi) / 2
    v = mid.zeta().log()
    if (v > three) == True: lo = mid
    elif (v < three) == True: hi = mid
    else: break
assert (lo.zeta().log() > three) == True and (hi.zeta().log() < three) == True
s = lo
print(f"s = sOf(3) in [{lo.lower()}, {hi.upper()}]  (bracket proved)")
print(f"3^s = {(arb(3) ** s).lower()}   (Cauchy radius must be below this)")

MU = [0] + [int(mobius(n)) for n in range(1, NMOB + 1)]
def P_odd(t):
    v = arb(0)
    for n in range(1, NMOB + 1):
        if MU[n]: v += arb(MU[n]) / arb(n) * (arb(n) * t).zeta().log()
    return v - arb(2) ** (-t)

# --- head -------------------------------------------------------------------
L = [arb(0)] * (KMAX + 1)
for j in range(1, KMAX + 1):
    L[j] = P_odd(s * j) / j
F = [arb(0)] * (KMAX + 1); F[0] = one
for k in range(1, KMAX + 1):
    F[k] = sum(arb(j) * L[j] * F[k - j] for j in range(1, k + 1)) / k
head, kbest = arb(0), 0
for k in range(1, KMAX + 1):
    v = F[k] * arb(3) ** k
    if (v.upper() > head.upper()) == True: head, kbest = v, k
print(f"HEAD  max_{{k<={KMAX}}} FkOdd_k 3^k <= {head.upper()}   (at k = {kbest})")

# --- tail -------------------------------------------------------------------
R = arb('3.1')
logM = arb(0)
for m in range(1, NMOB + 1):
    logM += R ** m * P_odd(arb(m) * s) / arb(m)
M = logM.exp()
tail = M * (three / R) ** (KMAX + 1)
print(f"TAIL  k > {KMAX}: M_R (3/R)^k <= {tail.upper()}")
CN = head.upper() if (head.upper() > tail.upper()) == True else tail.upper()
print(f"\nCN <= {CN}")
