#!/usr/bin/env python3
"""Certified CN with FkOdd k (sOf U) <= CN 3^-k for all k, at U = 3.

FkOdd k s = sum over odd n with Omega(n)=k of n^-s, whose generating function
is the odd Euler product
    sum_k FkOdd_k(s) z^k = prod_{p>=3} (1 - z p^-s)^-1,
so with L_j = P(js)/j, P(t) = sum_{p>=3} p^-t, the coefficients follow from the
exp recurrence F_0 = 1, F_k = (1/k) sum_{j<=k} j L_j F_{k-j} -- the same
machinery as hcoeff_recursion.py, and NOT by enumerating n (the n with
Omega(n)=k start at 3^k, far past any feasible cutoff).

HEAD k <= KMAX by the recursion; TAIL k > KMAX by Cauchy on |z| = R < 3^s,
    FkOdd_k <= M_R R^-k,  M_R = prod_{p>=3} (1 - R p^-s)^-1,
so FkOdd_k 3^k <= M_R (3/R)^k, decreasing once R > 3.

Usage: python3 cn_recursion.py [KMAX] [PCUT] [PREC]
"""
import sys
from mpmath import mp, mpf, log, quad, inf, exp
from sympy import primerange

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
PCUT = int(sys.argv[2]) if len(sys.argv) > 2 else 300000
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 30
mp.dps = PREC

# s = sOf(3)
lo, hi = mpf(1) + mpf(10)**(-30), mpf(60)
for _ in range(300):
    mid = (lo + hi) / 2
    if log(mp.zeta(mid)) > 3: lo = mid
    else: hi = mid
s = (lo + hi) / 2
print(f"U = 3,  sOf(U) = {s}")
print(f"3^s = {3**s}  (Cauchy radius must be < this)")

ps = list(primerange(3, PCUT))
def P(t):
    v = sum(mpf(p) ** (-t) for p in ps)
    if t < 3:                      # prime tail only matters for small t
        v += quad(lambda x: x ** (-t) / log(x), [PCUT, inf])
    return v

L = [mpf(0)] * (KMAX + 1)
for j in range(1, KMAX + 1):
    L[j] = P(s * j) / j

F = [mpf(0)] * (KMAX + 1); F[0] = mpf(1)
for k in range(1, KMAX + 1):
    F[k] = sum(j * L[j] * F[k - j] for j in range(1, k + 1)) / k

head = max(float(F[k] * mpf(3) ** k) for k in range(1, KMAX + 1))
kbest = max(range(1, KMAX + 1), key=lambda k: F[k] * mpf(3) ** k)
print(f"HEAD  max_{{k<={KMAX}}} FkOdd_k 3^k = {head:.4f}  (at k = {kbest})")

R = mpf('3.1')
logM = mpf(0)
for p in ps:
    logM -= log(1 - R * mpf(p) ** (-s))
# prime tail: -log(1 - R p^-s) <= 1.1 R p^-s for p > PCUT, summed over PRIMES
logM += mpf('1.1') * R * quad(lambda x: x ** (-s) / log(x), [PCUT, inf])
M = exp(logM)
tail = float(M * (3 / R) ** (KMAX + 1))
print(f"TAIL  k > {KMAX}:  M_R (3/R)^k <= {tail:.4f}   (M_R = {float(M):.1f}, R = {R})")
print()
print(f"CN <= {max(head, tail):.4f}")
