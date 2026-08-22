#!/usr/bin/env python3
"""Interval-certified NEARU: the near-region MAIN1/MAIN2 integrals, U = 3.

  |int_0^U MAIN1| <= sum_j |h_j(1)|          P(k-j+1, U)
  |int_0^U MAIN2| <= sum_j |b_j + 2g h_j(1)| P(k-j+1, 2U) / 2^(k-j+1)

with P the regularized lower incomplete gamma, and the FIRST-order-pole bounds
|h_j(1)| <= S_0 3^-j, |b_j| <= (j+1) S_1 3^-j from s0_/s1_recursion.py.  (Using
dom_j here instead would carry the third-order S = 14414 and is far too lossy.)

HEAD k <= KMAX exactly; TAIL k > KMAX by P(m,x) <= x^m/m!, which telescopes:
the MAIN1 sum is then at most S_0 e^(3U) 3^-k and MAIN2's 2^-(m+1) cancels
half of (2U)^m leaving (1/2)((k+1)S_1 + 2g S_0) e^(3U) 3^-k, so the ratio to
the (k+3)^3 3^-k budget is decreasing in k and the head maximum governs.

Supersedes nearu_bound.py, which computed the same quantity in mpmath.

Usage: python3 nearu_certified.py [KMAX] [PREC]
"""
import sys
from flint import arb, ctx

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 600
ctx.prec = PREC

U  = arb(3)
S0 = arb('44.5987')          # s0_cauchy.log
S1 = arb('490.1654')        # s1_cauchy.log (head + Cauchy tail)
g  = arb.const_euler()
one = arb(1)

def Preg(m, x):
    """regularized lower incomplete gamma P(m, x).

    NOTE the argument order: python-flint spells this z.gamma_lower(s), with
    the ARGUMENT as receiver and the ORDER as parameter -- the reverse of the
    usual P(s, z) notation."""
    return x.gamma_lower(arb(m), regularized=1)

worst, kbest = arb(0), 0
for k in range(1, KMAX + 1):
    m1 = arb(0); m2 = arb(0)
    for j in range(k + 1):
        m = k - j
        t3 = arb(3) ** (-j)
        m1 += S0 * t3 * Preg(m + 1, U)
        m2 += ((arb(j) + 1) * S1 + 2 * g * S0) * t3 \
              * Preg(m + 1, 2 * U) / arb(2) ** (m + 1)
    b = (arb(k) + 3) ** 3 * arb(3) ** (-k)
    r = (m1 + m2) / b
    if (r.upper() > worst.upper()) == True: worst, kbest = r, k

print(f"U = {U},  S_0 <= {S0},  S_1 <= {S1}")
print(f"HEAD  max_{{k<={KMAX}}} ratio <= {worst.upper()}   (at k = {kbest})")

env = (S0 * (3 * U).exp()
       + ((arb(KMAX) + 1) * S1 + 2 * g * S0) * (3 * U).exp() / 2) \
      / (arb(KMAX) + 3) ** 3
print(f"TAIL  k > {KMAX}: envelope ratio <= {env.upper()}")
NEARU = worst.upper() if (worst.upper() > env.upper()) == True else env.upper()
print(f"\nNEARU <= {NEARU}")
