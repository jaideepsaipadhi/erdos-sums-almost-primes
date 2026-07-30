#!/usr/bin/env python3
"""Certified f_k^odd, adapting numerics/certified.py by removing the p = 2
Euler factor.

The only change to the prime side is

    P_odd(t) = P(t) - 2^-t

applied after the log-zeta evaluation, so the pole handling at s -> 1+ (which
is what makes this computation nontrivial) is untouched.  The recursion that
builds P_k from the P_j is unchanged.

NOTE the pole is NOT removed by dropping p = 2: sum_{p>=3} p^-s still diverges
at s = 1, so f_k^odd has the same (log 1/(s-1))^k / k! growth near the pole
that f_k does.  Truncating the primes at any finite P destroys exactly this
behaviour, which is why naive enumeration badly misleads here.

Usage: python3 fodd_certified.py KMAX PREC
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "numerics"))
from flint import arb, acb, ctx

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 300
sys.argv = ["x", str(KMAX), str(PREC)]
import certified as C

def prime_zeta_odd(j, eps, sf):
    """P_odd(j(1+eps)) = P(j(1+eps)) - 2^{-j(1+eps)}."""
    t = arb(j) + arb(j) * eps
    return C.prime_zeta(j, eps, sf) - arb(2) ** (-t)

def all_Pk_odd(eps, sf, kmax):
    """Same recursion as certified.all_Pk but with the odd prime zeta."""
    ctx.prec = PREC
    Pj = [arb(0)] * (kmax + 2)
    for j in range(1, kmax + 2):
        Pj[j] = prime_zeta_odd(j, eps, sf)
    P = [arb(1)] + [arb(0)] * kmax
    for n in range(1, kmax + 1):
        acc = arb(0)
        for j in range(1, n + 1):
            acc += Pj[j] * P[n - j]
        P[n] = acc / n
    return P

if __name__ == "__main__":
    ctx.prec = PREC
    print("f_k^odd, certified, KMAX=%d PREC=%d" % (KMAX, PREC))
    print("(this is a scaffold: it exercises the odd prime zeta and the")
    print(" recursion.  The s-integration still needs certified.py's panel")
    print(" machinery, which is the next piece.)")
    for e in ["0.5", "0.1", "0.01", "0.001"]:
        eps = arb(e)
        sf = 1.0 + float(e) * 0.999
        P = all_Pk_odd(eps, sf, min(KMAX, 8))
        row = "  ".join("%9.5f" % float(P[k].mid()) for k in range(1, 7))
        print("  eps=%-6s P_k^odd(1+eps), k=1..6:  %s" % (e, row))
