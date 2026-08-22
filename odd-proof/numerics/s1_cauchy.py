#!/usr/bin/env python3
"""M_1 = sup_{|z|=R} |(d_s H)(1,z) (1-z/3)^2| for R = 4.5, giving the tail of S_1.

s1_recursion.py computes only the HEAD sum_{i<=NMAX} |g1_i| 3^i.  The tail
i > NMAX needs a Cauchy bound, which is what this supplies:
    |g1_i| <= M_1 R^-i   =>   sum_{i>NMAX} |g1_i| 3^i <= M_1 (3/R)^(NMAX+1)/(1-3/R).

Write G(z) = H(1,z)(1-z/3), bounded by M_0 in s0_cauchy.py.  Then
    (d_s H)(1,z)(1-z/3)^2 = G(z) * [(1-z/3) d_s log H (1,z)],
and the bracket is bounded termwise -- but only if the two pieces of each
prime's contribution are kept TOGETHER:
    f_p(z) = z log p [1/(p-1) - 1/(p-z)] = z log p (z-1)/((p-1)(p-z)),
which is O(log p / p^2).  Bounding the two pieces separately gives
O(log p / p) and diverges like log P; that cancellation is the whole point,
the same lesson as the factorwise bound in s0_cauchy.py.

The p = 3 term carries the pole and is cancelled by the explicit (1-z/3):
its contribution after cancellation is at most R log 3 / 3.

Usage: python3 s1_cauchy.py [PCUT] [PREC]
"""
import sys
from flint import arb, ctx
from sympy import primerange

PCUT = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 300
ctx.prec = PREC

one, R = arb(1), arb('4.5')
M0 = arb('348.41120457649094528661630450571098660276359846610104712098')  # s0_cauchy.log

# p = 2: H has NO (1-z/2)^-1 factor -- the Euler product runs over p >= 3 --
# so the p=2 contribution to d_s log H is just z d/ds log(1-2^-s), which at
# s = 1 is z log 2.  (An earlier version bounded a 1/(2-z) that does not exist,
# giving 6.86 in place of 3.12; safe but 2.2x loose.)
t2 = R * arb(2).log()
# p = 3: pole cancelled by the explicit factor, leaving |z log3 / 3|
t3 = R * arb(3).log() / 3
# p >= 5
trest = arb(0)
for p in primerange(5, PCUT):
    lp = arb(p).log()
    trest += R * lp * (R + 1) / ((arb(p) - one) * (arb(p) - R))
# tail p > PCUT: terms are <= R(R+1) log p / (p-1)(p-R) <= 2 R(R+1) log p / p^2,
# and sum_{p>P} log p/p^2 <= int_P^inf log x/x^2 dx = (1 + log P)/P
Pc = arb(PCUT)
ttail = 2 * R * (R + 1) * (one + Pc.log()) / Pc

B = t2 + t3 + trest + arb(0).union(ttail)
print(f"R = {R},  M_0 <= {M0}")
print(f"  p=2 term            <= {t2.upper()}")
print(f"  p=3 term (cancelled)<= {t3.upper()}")
print(f"  p>=5 sum (to {PCUT}) <= {trest.upper()}")
print(f"  p>{PCUT} tail        <= {ttail.upper()}")
print(f"  bracket bound B     <= {B.upper()}")
M1 = M0 * B
print(f"\nM_1 <= {M1.upper()}")

NMAX = 16
q = arb(3) / R
tail = M1 * q ** (NMAX + 1) / (one - q)
HEAD = arb('453.08379944484570437816698792067755090294197229672161723333')
print(f"\nHEAD (i <= {NMAX}, s1_head.log) <= {HEAD}")
print(f"TAIL (i >  {NMAX}, Cauchy)      <= {tail.upper()}")
print(f"S_1 = HEAD + TAIL              <= {(HEAD + tail).upper()}")
