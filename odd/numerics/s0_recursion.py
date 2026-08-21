#!/usr/bin/env python3
"""Certified S_0 = sum_i |a_i| 3^i, where a_i = [z^i] H(1,z)(1 - z/3).

This is the first-order-pole analogue of hcoeff_recursion.py's S.  It is what
bounds the TAIL terms sum_{j>k} h_j(1) and sum_{j>k} b_j 2^j, which PROOF.md
section 5.1 leaves as an unquantified "(lower order)".

Because H(1,z)(1-z/3) is analytic in |z| < 5 with the pole at z=3 cancelled,
    |h_j(1)| = 3^-j |sum_{i<=j} a_i 3^i| <= 3^-j S_0,
so  sum_{j>k} |h_j(1)| <= S_0 3^-k / 2,  with NO polynomial factor in k.

Usage: python3 s0_recursion.py [NMAX] [PCUT] [PREC]
"""
import sys
from flint import arb, ctx

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
PCUT = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 300
ctx.prec = PREC

def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n + 1) if s[i]]

primes = sieve(PCUT)
one = arb(1)
s = one  # evaluate at s = 1 exactly

# L_1 = log(1-2^-s) + sum_{p>=3} [p^-s + log(1-p^-s)]
L = [arb(0)] * (NMAX + 1)
acc = (one - arb(2) ** (-s)).log()
for p in primes:
    pm = arb(p) ** (-s)
    acc += pm + (one - pm).log()
# truncation: |sum_{p>PCUT}[p^-s+log(1-p^-s)]| <= sum_{p>PCUT} p^-2s <= 1/(PCUT-1)
tr = arb(1) / arb(PCUT - 1)
L[1] = acc + arb(0).union(tr).union(-tr)

# L_j = P(s,j)/j for j >= 2
for j in range(2, NMAX + 1):
    tot = arb(0)
    for p in primes:
        tot += arb(p) ** (-s * j)
    trj = arb(2) * arb(PCUT) ** (1 - j) / arb(j - 1)
    L[j] = (tot + arb(0).union(trj).union(-trj)) / arb(j)

# h_0 = 1,  h_m = (1/m) sum_{j=1}^m j L_j h_{m-j}
h = [arb(0)] * (NMAX + 1)
h[0] = one
for m in range(1, NMAX + 1):
    tot = arb(0)
    for j in range(1, m + 1):
        tot += arb(j) * L[j] * h[m - j]
    h[m] = tot / arb(m)

# a_i = h_i - h_{i-1}/3   (coefficients of H(1,z)(1 - z/3))
a = [arb(0)] * (NMAX + 1)
a[0] = h[0]
for i in range(1, NMAX + 1):
    a[i] = h[i] - h[i - 1] / arb(3)

print(f"{'i':>4} {'|h_i| 3^i':>22} {'|a_i| 3^i':>22} {'running S0':>22}")
run = arb(0)
for i in range(NMAX + 1):
    t = abs(a[i]) * arb(3) ** i
    run += t
    print(f"{i:>4} {str(abs(h[i]) * arb(3) ** i):>22} {str(t):>22} {str(run):>22}")

print()
print(f"HEAD  sum_{{i<={NMAX}}} |a_i| 3^i <= {run.upper()}")
print()
print("For the tail i > NMAX, Cauchy on |z| = 4.5 for H(1,z)(1-z/3):")
print("  |a_i| <= M0 4.5^-i, so sum_{i>NMAX} |a_i| 3^i <= M0 (2/3)^(NMAX+1) / (1/3)")
print("  -> run s0_cauchy.py for a certified M0")
