#!/usr/bin/env python3
"""Certified f_k^odd via certified.py's panel machinery.

Three changes from the even case:
  all_Pk        -> all_Pk_odd      (P_odd(t) = P(t) - 2^-t)
  tail_large_s  -> 3^-s form       (P_odd(s) <= 1.91 * 3^-s for s >= 2,
                                    verified: P_odd(s)*3^s decreases 1.820 at
                                    s=2 toward 1 as s grows)
  panel_gl_error-> uses all_Pk_odd
tail_near_1 is unchanged: it depends only on UHI and k!, not on prime data.

Usage: python3 fodd_run.py KMAX PREC
"""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "numerics"))
from flint import arb, ctx

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 400
sys.argv = ["x", str(KMAX), str(PREC)]
import certified as C

C_ODD = arb("1.91")

def prime_zeta_odd(j, eps, sf):
    t = arb(j) + arb(j) * eps
    return C.prime_zeta(j, eps, sf) - arb(2) ** (-t)

def all_Pk_odd(eps, sf, kmax):
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

def panel_gl_error_odd(a, b, kmax):
    sig_eps = arb(C.DELTA).cos() * arb(-(b + C.EXT)).exp()
    Pk = all_Pk_odd(sig_eps, 1.0, kmax)
    eamp = arb(-(a - C.EXT)).exp()
    out = []
    for k in range(kmax + 1):
        M = (arb(Pk[k].mid()) + arb(Pk[k].rad())) * eamp
        e = C.CQ * M * arb(C.H / 2)
        out.append(arb(0).union(e.union(-e)))
    return out

def tail_large_s_odd(k):
    # S0 = 1 + exp(-ULO) with ULO = -5.10, so S0 = 166.0 -- genuinely large s,
    # NOT s near 1.  The constant C_ODD = 1.91 in P_odd(s) <= C_ODD 3^-s holds
    # comfortably there (the ratio P_odd(s)/3^-s falls to 1.0000 by s = 20);
    # it is FALSE for s < 2, where the ratio reaches 7.2 at s = 1.05, but that
    # range is covered by the panel quadrature, not by this tail.
    S0 = 1 + arb(-C.ULO).exp()
    e = C_ODD ** k * arb(3) ** (-k * S0) / (k * arb(3).log())
    return arb(0).union(e.union(-e))

def main():
    ctx.prec = PREC
    t0 = time.time()
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
            Pk = all_Pk_odd(eu, sf, KMAX)
            we = wq * eu
            for k in range(1, KMAX + 1):
                fk[k] += we * Pk[k]
        gerr = panel_gl_error_odd(a, b, KMAX)
        for k in range(1, KMAX + 1):
            fk[k] += gerr[k]
        if (pi + 1) % 25 == 0:
            el = time.time() - t0
            print("panel %d/%d  t=%.0fs  eta=%.0fs"
                  % (pi + 1, C.NPANEL, el, el / (pi + 1) * (C.NPANEL - pi - 1)),
                  file=sys.stderr, flush=True)
    for k in range(2, KMAX + 1):
        fk[k] += tail_large_s_odd(k) + C.tail_near_1(k)
    print("k   f_k^odd")
    for k in range(1, KMAX + 1):
        print("%2d  %s" % (k, fk[k].str(20)), flush=True)
    print()
    dec = all((fk[k] - fk[k + 1]) > 0 for k in range(2, KMAX))
    print("f_k^odd strictly decreasing on [2,%d]: %s" % (KMAX, dec))
    inc = all((fk[k + 1] - fk[k]) > 0 for k in range(2, KMAX))
    print("f_k^odd strictly increasing on [2,%d]: %s" % (KMAX, inc))

if __name__ == "__main__":
    main()
