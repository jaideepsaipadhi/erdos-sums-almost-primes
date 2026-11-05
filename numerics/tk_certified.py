#!/usr/bin/env python3
"""Certify eq:Tk-certified, 2^k |T_k| <= 1.45/k for k >= 900.

The other constant in Proposition 6.1 with no generating artifact.  Like
101.245 it existed only as a hardcoded literal -- in check_paper_phi.py,
k1_far_range.py and TRUSTED-BASE.md -- and the only other 1.45 in the
repository (certified.py's DELTA, the quadrature ellipse's semi-minor axis) is
an unrelated coincidence that makes the literal look sourced when it is not.

The bound is elementary once T_k is unfolded.  By eq:Tk-def and eq:Ik-def,
with [z^k]F(s,z) = sum_{Omega(n)=k} n^-s,

    T_k = f_k - I_k = int_2^inf sum_{Omega(n)=k} n^-s ds
        = sum_{Omega(n)=k} n^-2 / log n,

all terms positive, so T_k > 0 and no absolute values are lost.  Every n with
Omega(n) = k has n >= 2^k, hence log n >= k log 2 and

    2^k T_k <= 2^k P_k(2) / (k log 2),        P_k(2) := [z^k] F(2,z).

So it suffices that 2^k P_k(2) <= 1.45 log 2 = 1.005135 for every k >= 900.
F(2,z) = prod_p (1 - z p^-2)^-1 is holomorphic on |z| < 4, so Cauchy on
|z| = R gives P_k(2) <= M(R) R^-k with

    M(R) = sup_{|z|=R} |F(2,z)| = prod_p (1 - R p^-2)^-1

(the supremum is at z = R, each factor being maximized there), and therefore

    2^k P_k(2) <= M(R) (2/R)^k.

At R = 3 this is M(3)(2/3)^k, which at k = 900 is below 10^-150.  The bound
is true with room to spare of that order; it is stated as 1.45/k because that
is the form the criterion consumes, not because 1.45 is near optimal.

The margin is reported both ways: the largest k at which the bound could
conceivably fail, and the actual value of the envelope at k = 900.

    python3 tk_certified.py            # -> tk.log, instant
"""
import sys
from flint import arb, ctx

ctx.prec = 300
STATED = arb("1.45")
KMIN = 900
R = arb(3)


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


PCUT = 2000000
PS = primes_upto(PCUT)
# M(R) = prod_p (1 - R/p^2)^-1.  Tail over p > PCUT: each factor is
# (1 - R/p^2)^-1 <= exp(2R/p^2) for p^2 >= 2R, so the tail is at most
# exp(2R sum_{p>P} p^-2) <= exp(2R / (P log P)).
M = arb(1)
for p in PS:
    pa = arb(p)
    M *= 1 / (1 - R / (pa * pa))
Pa = arb(PCUT)
M *= (2 * R / (Pa * Pa.log())).exp()
print("# M(3) = sup_{|z|=3} |F(2,z)| <= %s   (primes to %d + Euler tail)"
      % (M.upper().str(10), PCUT))

log2 = arb(2).log()
need = STATED * log2
print("# need 2^k P_k(2) <= 1.45 log 2 = %s for every k >= %d"
      % (need.lower().str(10), KMIN))

# envelope at k = KMIN
env = M * (arb(2) / R) ** KMIN
print("# envelope M(3)(2/3)^k at k = %d: <= %s" % (KMIN, env.upper().str(6)))

# the largest k at which the envelope could exceed the requirement
k = 1
while float((M * (arb(2) / R) ** k).upper()) > float(need.lower()):
    k += 1
print("# envelope drops below the requirement at k = %d, far below %d" % (k, KMIN))

ok = float(env.upper()) <= float(need.lower())
print()
print("stated      2^k |T_k| <= 1.45/k   (k >= %d)" % KMIN)
print("certified   2^k  T_k  <= M(3)(2/3)^k / (k log 2) <= %s / k"
      % (env / log2).upper().str(6))
print("VERDICT: %s" % ("stated bound HOLDS, with margin of order 10^-150"
                       if ok else "NOT established"))
sys.exit(0 if ok else 1)
