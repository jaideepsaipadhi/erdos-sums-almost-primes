#!/usr/bin/env python3
"""Certified S_1 = sum_i |g1_i| 3^i, g1_i = [z^i] (d_s H)(1,z) (1 - z/3)^2.

Bounds the tail sum_{j>k} b_j 2^j, where b_j = h_j'(1), the other term
PROOF.md section 5.1 leaves as "(lower order)".

d_s H = H D_1 has a pole of order 2 at z = 3^s (order 1 from H, order 1 from
D_1), so (1-z/3)^2 cancels it and the negative-binomial unwinding gives
    |b_j| <= 3^-j (j+1) S_1,
whence sum_{j>k} |b_j| 2^j <= S_1 sum_{j>k} (j+1) (2/3)^j -- linear in k, not
cubic, so far inside the C (k+3)^3 3^-k budget.

Usage: python3 s1_recursion.py [NMAX] [PCUT] [PREC]
"""
import sys
from flint import arb, ctx

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
PCUT = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 300
ctx.prec = PREC

def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n + 1) if s[i]]

primes = sieve(PCUT)
one = arb(1); s = one

# L_j and L_j' at s = 1
L  = [arb(0)] * (NMAX + 1)
Lp = [arb(0)] * (NMAX + 1)
acc = (one - arb(2) ** (-s)).log()
for p in primes:
    pm = arb(p) ** (-s)
    acc += pm + (one - pm).log()
tr = one / arb(PCUT - 1)
L[1] = acc + arb(0).union(tr).union(-tr)

accp = arb(2).log() / (arb(2) ** s - one)
for p in primes:
    ps = arb(p) ** s
    accp += arb(p).log() / (ps * (ps - one))
trp = arb(2) * arb(PCUT).log() / arb(PCUT)
Lp[1] = accp + arb(0).union(trp).union(-trp)

for j in range(2, NMAX + 1):
    tot = arb(0); totp = arb(0)
    for p in primes:
        pj = arb(p) ** (-s * j)
        tot += pj
        totp += arb(p).log() * pj
    trj = arb(2) * arb(PCUT) ** (1 - j) / arb(j - 1)
    L[j]  = (tot + arb(0).union(trj).union(-trj)) / arb(j)
    Lp[j] = -(totp + arb(0).union(trj).union(-trj))

# h_m, then (d_s H)_i = sum_m h_m (D_1)_{i-m} with (D_1)_j = Lp[j]
h = [arb(0)] * (NMAX + 1); h[0] = one
for m in range(1, NMAX + 1):
    tot = arb(0)
    for j in range(1, m + 1):
        tot += arb(j) * L[j] * h[m - j]
    h[m] = tot / arb(m)

d = [arb(0)] * (NMAX + 1)
for i in range(NMAX + 1):
    tot = arb(0)
    for m in range(i + 1):
        if i - m >= 1:
            tot += h[m] * Lp[i - m]
    d[i] = tot

# g1 = d * (1 - z/3)^2 = d * (1 - 2z/3 + z^2/9)
g1 = [arb(0)] * (NMAX + 1)
for i in range(NMAX + 1):
    v = d[i]
    if i >= 1: v -= arb(2) * d[i - 1] / arb(3)
    if i >= 2: v += d[i - 2] / arb(9)
    g1[i] = v

print(f"{'i':>4} {'|d_i| 3^i':>20} {'|g1_i| 3^i':>20} {'running S1':>20}")
run = arb(0)
for i in range(NMAX + 1):
    t = abs(g1[i]) * arb(3) ** i
    run += t
    print(f"{i:>4} {str(abs(d[i]) * arb(3) ** i):>20} {str(t):>20} {str(run):>20}")
print()
print(f"HEAD sum_{{i<={NMAX}}} |g1_i| 3^i <= {run.upper()}")
