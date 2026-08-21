#!/usr/bin/env python3
"""Certified CN with FkOdd k s <= CN 3^-k for all k, at s = sOf(U), U = 3.

The generating function of FkOdd is the odd Euler product
    sum_k FkOdd_k(s) z^k = prod_{p>=3} (1 - z p^-s)^-1,
analytic in |z| < 3^s.  Cauchy on |z| = 3 (legitimate since 3^s > 3 for s > 1)
gives, with all coefficients positive,
    FkOdd_k(s) <= M 3^-k,   M = prod_{p>=3} (1 - 3 p^-s)^-1.

Usage: python3 cn_bound.py [U] [PCUT] [PREC]
"""
import sys
from flint import arb, ctx

Uval = arb(sys.argv[1]) if len(sys.argv) > 1 else arb(3)
PCUT = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 300
ctx.prec = PREC

def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n + 1) if s[i]]

primes = sieve(PCUT)
one = arb(1)

# s = sOf(U): solve log zeta(s) = U by bisection on [1+eps, 60]
def zetaR(s):
    tot = arb(0)
    for n in range(1, 400000):
        tot += arb(n) ** (-s)
    # tail n > N: int_N^inf x^-s dx = N^(1-s)/(s-1)
    N = arb(400000)
    tail = N ** (1 - s) / (s - one)
    return tot + arb(0).union(tail).union(arb(0))

lo, hi = one + arb(10) ** (-20), arb(60)
for _ in range(200):
    mid = (lo + hi) / 2
    if zetaR(mid).log() > Uval: lo = mid
    else: hi = mid
s = (lo + hi) / 2
print("U =", Uval, " sOf(U) =", s)
print("3^s =", arb(3) ** s, " (must exceed 3)")

# M = prod_{p>=3} (1 - 3 p^-s)^-1
logM = arb(0)
for p in primes:
    x = arb(3) * arb(p) ** (-s)
    logM -= (one - x).log()
# tail p > PCUT: -log(1-3p^-s) <= 3 p^-s (1+eps); sum <= 3 * PCUT^(1-s)/(s-1) * 1.1
tail = arb(3) * arb(PCUT) ** (1 - s) / (s - one) * arb(11) / arb(10)
logM += arb(0).union(tail).union(arb(0))
print("CN <=", logM.exp().upper())
