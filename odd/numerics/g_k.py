#!/usr/bin/env python3
"""g_k = int_1^inf 2^-s P_k(s) ds, the single new object the odd case needs.

f_k^odd = f_k - g_{k-1}  (exact), so the odd conjecture is
    f_k - f_{k+1} + g_k - g_{k-1} > 0.

Uses certified.py's panel machinery with the extra weight 2^-s.
Usage: python3 g_k.py KMAX PREC
"""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "numerics"))
from flint import arb, ctx
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 400
sys.argv = ["x", str(KMAX), str(PREC)]
import certified as C

def main():
    ctx.prec = PREC
    t0 = time.time()
    nodes, weights = C.gl_certified(C.NGL)
    g = [arb(0)] * (KMAX + 1)
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
            Pk, _ = C.all_Pk(eu, sf, KMAX)
            s = arb(1) + eu
            w2 = arb(2) ** (-s)
            we = wq * eu * w2
            for k in range(0, KMAX + 1):
                g[k] += we * Pk[k]
        if (pi + 1) % 25 == 0:
            el = time.time() - t0
            print("panel %d/%d t=%.0fs eta=%.0fs"
                  % (pi + 1, C.NPANEL, el, el / (pi + 1) * (C.NPANEL - pi - 1)),
                  file=sys.stderr, flush=True)
    print("k    g_k                      g_k - 1/2         (g_k - 1/2) * 2^k")
    for k in range(0, KMAX + 1):
        v = float(g[k].mid())
        print("%2d   %.18f   %+.6e   %+.6f" % (k, v, v - 0.5, (v - 0.5) * 2**k))

if __name__ == "__main__":
    main()
