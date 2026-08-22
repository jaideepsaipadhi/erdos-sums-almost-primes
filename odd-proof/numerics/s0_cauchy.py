#!/usr/bin/env python3
"""M0 = sup_{|z|=R} |H(1,z)(1 - z/3)| for R = 4.5, by the Euler product.

The p=3 factor is exactly cancelled by (1-z/3):
    H(1,z)(1-z/3) = (1/3)^z prod_{p>=5} (1 - z/p)^-1 (1-1/p)^z
so with z = R e^{i th}, c = cos th, x = R/p:
    log|.| = -R c log 3 + sum_{p>=5} f_p,
    f_p = -(1/2) log(1 - 2 x c + x^2) + R c log(1 - 1/p).
The 1/p terms of the two pieces cancel, so f_p = O(R^2/p^2) uniformly in th;
primes up to PSPLIT are evaluated as intervals over a th-grid, the rest bounded.

Usage: python3 s0_cauchy.py [R_num] [R_den] [NTH] [PSPLIT] [PREC]
"""
import sys
from flint import arb, ctx

RN     = int(sys.argv[1]) if len(sys.argv) > 1 else 9
RD     = int(sys.argv[2]) if len(sys.argv) > 2 else 2
NTH    = int(sys.argv[3]) if len(sys.argv) > 3 else 400
PSPLIT = int(sys.argv[4]) if len(sys.argv) > 4 else 2000
PREC   = int(sys.argv[5]) if len(sys.argv) > 5 else 300
ctx.prec = PREC

def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(5, n + 1) if s[i]]

primes = sieve(PSPLIT)
one = arb(1); R = arb(RN) / arb(RD)
pi = arb.pi()

# theta grid: c = cos th ranges over [-1,1]; enclose each cell.
# cos is monotone on [0,pi] and on [pi,2pi], so endpoint union encloses it
# EXCEPT on a cell straddling pi, where the minimum -1 is interior; the test
# below adds it.  (With NTH even, pi lands on a cell boundary and the test
# never fires; it is needed for odd NTH.  Verified by fine sampling at
# NTH = 399, 400, 401: no sample falls outside the enclosure.)
best = None
for t in range(NTH):
    lo = pi * arb(2 * t) / arb(NTH)
    hi = pi * arb(2 * (t + 1)) / arb(NTH)
    # enclose cos over the cell by its endpoints union the extremes it may contain
    cs = lo.cos().union(hi.cos())
    if (lo <= pi) and (pi <= hi): cs = cs.union(arb(-1))
    if t == 0 or (lo <= 2 * pi and 2 * pi <= hi): cs = cs.union(arb(1))
    c = cs
    tot = -R * c * arb(3).log()
    for p in primes:
        x = R / arb(p)
        tot += -(one - arb(2) * x * c + x * x).log() / arb(2)
        tot += R * c * (one - one / arb(p)).log()
    # tail p > PSPLIT: |f_p| <= K/p^2 with K = R^2 (1 + R/PSPLIT)/(1-R/PSPLIT)^2 + R/2
    xs = R / arb(PSPLIT)
    K = R * R * (one + xs) / (one - xs) ** 2 + R / arb(2)
    tail = K / arb(PSPLIT - 1)
    tot += arb(0).union(tail).union(-tail)
    v = tot.exp()
    best = v if best is None else best.union(v)

M0 = best.upper()
print("R =", R)
print("M0 <=", M0)

# Combine with the head from s0_recursion.py so S_0 itself appears in a log.
HEAD = arb('43.537789114875634')      # s0_head.log: sum_{i<=16} |a_i| 3^i
NMAX = 16
q = arb(3) / R
tail = M0 * q ** (NMAX + 1) / (one - q)
print("HEAD (i <= %d, from s0_head.log) <= %s" % (NMAX, HEAD))
print("TAIL (i >  %d, Cauchy at R)      <= %s" % (NMAX, tail))
print("S_0 = HEAD + TAIL                <= %s" % (HEAD + tail).upper())
