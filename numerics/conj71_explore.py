#!/usr/bin/env python3
"""NON-CERTIFIED exploration of Conjecture 7.1 for P beyond the two proved cases.

Conjecture 7.1: for P with thin complement and least element q, the sequence
f_k^P is eventually INCREASING iff q = 2.

The paper proves the two extremes, P = all primes (q=2, increasing) and
P = {p>=3} (q=3, decreasing).  Everything between is open.  Removing finitely
many primes keeps the complement thin trivially, so these are legitimate test
cases, and two of them probe exactly what neither proved case does:

    drop {3}      q = 2, nontrivial complement  -> conjecture says INCREASING
    drop {2,3}    q = 5                         -> says DECREASING
    drop {5}      q = 2                         -> says INCREASING
    drop {2}      q = 3   (the proved odd case) -> says DECREASING, a control

This reuses the certified panel/quadrature machinery but NOT its error terms,
which were derived for the full and odd cases.  Midpoints only; this is
evidence, not a certificate.

Usage: python3 conj71_explore.py [KMAX] [PREC]
"""
import sys, os, time
sys.path.insert(0, "/home/claude/erdos-sums-almost-primes/numerics")
from flint import arb, ctx

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 200
sys.argv = ["x", str(KMAX), str(PREC)]
import certified as C

def make_all_Pk(drop):
    """all_Pk for P = primes minus `drop`."""
    def all_Pk_P(eps, sf, kmax):
        Pj = [arb(0)] * (kmax + 2)
        for j in range(1, kmax + 2):
            t = arb(j) + arb(j) * eps
            v = C.prime_zeta(j, eps, sf)
            for p in drop:
                v = v - arb(p) ** (-t)
            Pj[j] = v
        P = [arb(1)] + [arb(0)] * kmax
        for n in range(1, kmax + 1):
            acc = arb(0)
            for j in range(1, n + 1):
                acc += Pj[j] * P[n - j]
            P[n] = acc / n
        return P
    return all_Pk_P

def fk_for(drop):
    all_Pk_P = make_all_Pk(drop)
    nodes, weights = C.gl_certified(C.NGL)
    fk = [arb(0)] * (KMAX + 1)
    for pi in range(C.NPANEL):
        a, b = float(C.EDGES[pi]), float(C.EDGES[pi + 1])
        ha = (arb(b) - arb(a)) / 2
        mid = (arb(b) + arb(a)) / 2
        for X, W in zip(nodes, weights):
            u = ha * X + mid
            wq = ha * W
            eu = (-u).exp()
            fe = float(eu.mid())
            sf = 1.0 + fe * 0.999 if fe > 1e-300 else 1.0
            Pk = all_Pk_P(eu, sf, KMAX)
            we = wq * eu
            for k in range(1, KMAX + 1):
                fk[k] += we * Pk[k]
    return fk

CASES = [("drop {2}      q=3  (proved: decreasing)", (2,)),
         ("drop {3}      q=2  (OPEN: says increasing)", (3,)),
         ("drop {2,3}    q=5  (OPEN: says decreasing)", (2, 3)),
         ("drop {5}      q=2  (OPEN: says increasing)", (5,)),
         ("drop nothing  q=2  (proved: increasing)", ())]

ctx.prec = PREC
print("KMAX=%d PREC=%d   NON-CERTIFIED midpoints\n" % (KMAX, PREC))
for label, drop in CASES:
    t0 = time.time()
    fk = fk_for(drop)
    v = [float(fk[k].mid()) for k in range(1, KMAX + 1)]
    d = [v[i+1] - v[i] for i in range(len(v) - 1)]
    # the sign of the LAST few differences is the asymptotic direction; the
    # earlier ones are pre-asymptotic and say nothing (the proved increasing
    # case is itself not monotone until k = 6)
    tail = d[-4:]
    inc = all(x > 0 for x in tail); dec = all(x < 0 for x in tail)
    verdict = "INCREASING" if inc else ("DECREASING" if dec else "NOT SETTLED")
    # last k at which the sign differs from the final sign
    sgn = [1 if x > 0 else -1 for x in d]
    turn = None
    for i in range(len(sgn) - 1, 0, -1):
        if sgn[i] != sgn[-1]:
            turn = i + 2     # d[i] is f_{i+2} - f_{i+1}
            break
    print("%-42s  %-12s  turns at k=%s   (%.0fs)"
          % (label, verdict, turn if turn else "<=2", time.time() - t0))
    print("   f_k, k=%d..%d: %s" % (KMAX-4, KMAX,
          " ".join("%.9f" % x for x in v[-5:])))
    print("   signs k=2..%d: %s" % (KMAX, "".join("+" if x > 0 else "-" for x in sgn)))
    print()
