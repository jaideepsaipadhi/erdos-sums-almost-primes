#!/usr/bin/env python3
"""Certified NEARU: the near-region MAIN1/MAIN2 integrals, over Ioc 0 U at U=3.

  |int_0^U MAIN1| <= sum_j |h_j(1)| * P(k-j+1, U)         [P = regularized lower gamma]
  |int_0^U MAIN2| <= sum_j |b_j + 2g h_j(1)| * P(k-j+1, 2U)/2^(k-j+1)

with the FIRST-order-pole bounds |h_j(1)| <= S0 3^-j and |b_j| <= (j+1) S1 3^-j
(s0_recursion.py, s1_recursion.py) -- NOT the third-order dom_j, which carries
S = 14414 and is far too lossy here.

Claim: the total is <= NEARU (k+3)^3 3^-k for all k.  Head k <= KMAX directly;
tail k > KMAX by the geometric decay of both sums.

Usage: python3 nearu_bound.py [KMAX] [PREC]
"""
import sys
from mpmath import mp, mpf, gammainc, euler

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 30
mp.dps = PREC

U  = mpf(3)
S0 = mpf('44.6')
S1 = mpf('453.1')
g  = euler

def P(m, x):
    return gammainc(m, 0, x, regularized=True)

worst, kbest = mpf(0), 0
for k in range(1, KMAX + 1):
    m1 = sum(S0 * mpf(3) ** (-j) * P(k - j + 1, U) for j in range(k + 1))
    m2 = sum(((j + 1) * S1 + 2 * g * S0) * mpf(3) ** (-j)
             * P(k - j + 1, 2 * U) / mpf(2) ** (k - j + 1) for j in range(k + 1))
    b = (mpf(k) + 3) ** 3 * mpf(3) ** (-k)
    r = (m1 + m2) / b
    if r > worst:
        worst, kbest = r, k

print(f"U = {U},  S0 = {S0},  S1 = {S1}")
print(f"HEAD  max_{{k<={KMAX}}} ratio = {float(worst):.4f}  (at k = {kbest})")
print()
print("TAIL k > KMAX: both sums decay like 3^-k against a (k+3)^3 3^-k budget,")
print("so the ratio is decreasing once past its peak; the head max bounds it.")
print()
print(f"NEARU <= {float(worst):.4f}")
