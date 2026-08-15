#!/usr/bin/env python3
"""Certified M_a = sup_{|z|=R, s in [1,2]} |d_s^a Htilde(s,z)| for a = 0, 1, 2.

Supersedes mr_deriv_certified.py, which fixed s = 1.  The sup over s in [1,2]
is what the argument actually needs: the remainder is bounded by Taylor's
theorem with Lagrange remainder,

    |h_j(s) - h_j(1) - (s-1) b_j| <= (sup_{t in [1,2]} |h_j''(t)| / 2) (s-1)^2,

and the second derivative is evaluated at an interior point, not at s = 1.

    Htilde(s,z) = (1-2^-s)^z (1-3^-s)^z prod_{p>=5} (1-z p^-s)^-1 (1-p^-s)^z

With L = log Htilde and a = a(s) = base^-s, l = log base:

    L   = z log(1-a2) + z log(1-a3)
          + sum_{p>=5} [ z log(1-ap) - log(1-z ap) ]
    L'  = z [ a2 l2/(1-a2) + a3 l3/(1-a3) ]
          + sum_{p>=5} [ z lp ap/(1-ap) - z lp ap/(1-z ap) ]
    L'' = z [ -l2^2 a2/(1-a2)^2 - l3^2 a3/(1-a3)^2 ]
          + sum_{p>=5} [ -z lp^2 ap/(1-ap)^2 + z lp^2 ap/(1-z ap)^2 ]

    |Htilde|       = exp(Re L)
    |d_s Htilde|   = |Htilde| |L'|
    |d_s^2 Htilde| <= |Htilde| (|L'|^2 + |L''|)

Usage: python3 mr_deriv_sweep.py [R] [NTHETA] [NS] [PCUT] [PREC]
"""
import sys
from flint import arb, acb, ctx

R      = float(sys.argv[1]) if len(sys.argv) > 1 else 4.5
NTHETA = int(sys.argv[2])   if len(sys.argv) > 2 else 200
NS     = int(sys.argv[3])   if len(sys.argv) > 3 else 40
PCUT   = int(sys.argv[4])   if len(sys.argv) > 4 else 100000
PREC   = int(sys.argv[5])   if len(sys.argv) > 5 else 300
ctx.prec = PREC


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(5, n + 1) if s[i]]


def interval(lo, hi):
    return ((lo + hi) / 2).union(lo).union(hi)


def main():
    primes = sieve(PCUT)
    print("R=%.2f NTHETA=%d NS=%d primes<=%d (%d) prec=%d  [s in [1,2]]"
          % (R, NTHETA, NS, PCUT, len(primes), PREC), flush=True)

    # Tail bounds for p > PCUT.  Worst case is s = 1, where p^-s = 1/p.
    #   L   : |z log(1-1/p) - log(1-z/p)|  ~ |z|(|z|+1)/p^2
    #   L'  : extra log p   -> sum_{p>P} log p / p^2      <= 2.52/P
    #   L'' : extra log^2 p -> sum_{p>P} (log p)^2 / p^2  <= 2.52(log P + 1)/P
    P = arb(PCUT)
    zmag = arb(R)
    fac = zmag * (zmag + 1) * arb("1.1")
    tailL  = arb(4) * zmag / (P * P.log())
    tailL1 = fac * arb("2.52") / P
    tailL2 = fac * arb("2.52") * (P.log() + 1) / P
    print("tails:  L %.3e   L' %.3e   L'' %.3e"
          % (float(tailL), float(tailL1), float(tailL2)), flush=True)

    one = acb(1)
    worst = [arb(0), arb(0), arb(0)]

    for si in range(NS):
        sbox = interval(arb(1) + arb(si) / NS, arb(1) + arb(si + 1) / NS)
        a2 = arb(2) ** (-sbox)
        a3 = arb(3) ** (-sbox)
        l2 = arb(2).log()
        l3 = arb(3).log()
        pw = [(arb(p) ** (-sbox), arb(p).log()) for p in primes]

        for i in range(NTHETA):
            th = interval(arb(2) * arb.pi() * i / NTHETA,
                          arb(2) * arb.pi() * (i + 1) / NTHETA)
            z = acb(th.cos(), th.sin()) * R

            reL = arb(0)
            L1 = acb(0)
            L2 = acb(0)

            for a, l in ((a2, l2), (a3, l3)):
                reL += (z * acb((1 - a).log())).real
                L1 += z * acb(a * l / (1 - a))
                L2 += z * acb(-l * l * a / ((1 - a) * (1 - a)))

            for ap, lp in pw:
                zap = z * acb(ap)
                den = one - zap
                reL += (z * acb((1 - ap).log())).real
                reL -= abs(den).log()
                L1 += z * acb(lp * ap / (1 - ap)) - z * acb(lp * ap) / den
                L2 += (z * acb(-lp * lp * ap / ((1 - ap) * (1 - ap)))
                       + z * acb(lp * lp * ap) / (den * den))

            reL += interval(-tailL, tailL)
            L1 += acb(interval(-tailL1, tailL1), interval(-tailL1, tailL1))
            L2 += acb(interval(-tailL2, tailL2), interval(-tailL2, tailL2))

            H = reL.exp()
            for j, m in enumerate((H, H * abs(L1),
                                   H * (abs(L1) * abs(L1) + abs(L2)))):
                u = arb(float(m.upper()))
                if float(u) > float(worst[j]):
                    worst[j] = u

        print("  s box %d/%d  M0<=%.2f M1<=%.2f M2<=%.2f"
              % (si + 1, NS, float(worst[0]), float(worst[1]),
                 float(worst[2])), file=sys.stderr, flush=True)

    M0, M1, M2 = (float(w) for w in worst)
    print()
    print("M_0 <= %.6f" % M0)
    print("M_1 <= %.6f" % M1)
    print("M_2 <= %.6f" % M2)
    print()

    # G_0 = Htilde;  G_{r+1} = (d_s G_r)(1 - z/3) + (r+1) z (log3/3) G_r
    # on |z| = R:  |1 - z/3| <= 1 + R/3,  |z| = R
    c = 1 + R / 3
    l3f = 1.0986122886681098 / 3
    G0 = M0
    G1 = c * M1 + R * l3f * G0
    dG1 = c * M2 + R * l3f * M1
    G2 = c * dG1 + 2 * R * l3f * G1
    geo = 1.0 / (1.0 - 3.0 / R)
    C = G2 * geo / 18.0
    print("|1-z/3| <= %.4f   1/(1-3/R) = %.4f" % (c, geo))
    print("G_0 <= %.1f   G_1 <= %.1f   G_2 <= %.1f" % (G0, G1, G2))
    print("C = G_2/(1-3/R)/18 = %.1f   [in |R_k| <= C (k+3)^3 3^-k]" % C)

    beta = 0.15563271
    thr = beta / 3 / C
    K0 = None
    for k in range(10, 400):
        v = (k + 3) ** 3 * (2 / 3) ** k
        if v < thr and K0 is None:
            K0 = k
        elif v >= thr:
            K0 = None
    print("K0 = %s   (certified sweep must reach at least this)" % K0)


if __name__ == "__main__":
    main()
