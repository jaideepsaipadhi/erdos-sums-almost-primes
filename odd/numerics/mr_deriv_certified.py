#!/usr/bin/env python3
"""Certified M_a = sup_{|z|=R} |d_s^a Htilde(1,z)| for a = 0, 1, 2.

These are the sups the coefficient bound needs:

    d_s^r H(1,z) = G_r(z) / (1 - z/3)^(r+1),   G_r analytic in |z| < 5,

and |[z^i] d_s^r H(1,z)| <= (M_r/(1-3/R)) ((i+r)^r/r!) 3^-i.  With r = 2 this
is the dominant term of the remainder, giving |R_k| <= C k^3 3^-k.

Unlike mr_certified.py this fixes s = 1 rather than sweeping s in [1,2]: the
coefficients h_j^(r)(1) are taken AT s = 1, so no uniformity in s is needed.

    Htilde(s,z) = (1-2^-s)^z (1-3^-s)^z prod_{p>=5} (1-z p^-s)^-1 (1-p^-s)^z

so with L = log Htilde,

    L  = z log(1-2^-s) + z log(1-3^-s)
         + sum_{p>=5} [ z log(1-p^-s) - log(1-z p^-s) ]

    L' = z [ a2 l2/(1-a2) + a3 l3/(1-a3) ]
         + sum_{p>=5} [ z lp ap/(1-ap) - z lp ap/(1-z ap) ]

    L''= z [ -l2^2 a2/(1-a2)^2 - l3^2 a3/(1-a3)^2 ]
         + sum_{p>=5} [ -z lp^2 ap/(1-ap)^2 + z lp^2 ap/(1-z ap)^2 ]

writing ap = p^-s, lp = log p.  Then

    |Htilde|      = exp(Re L)
    |d_s Htilde|  = |Htilde| |L'|
    |d_s^2 Htilde|= |Htilde| |L'^2 + L''| <= |Htilde| (|L'|^2 + |L''|)

Usage: python3 mr_deriv_certified.py [R] [NTHETA] [PCUT] [PREC]
"""
import sys
from flint import arb, acb, ctx

R      = float(sys.argv[1]) if len(sys.argv) > 1 else 4.5
NTHETA = int(sys.argv[2])   if len(sys.argv) > 2 else 400
PCUT   = int(sys.argv[3])   if len(sys.argv) > 3 else 100000
PREC   = int(sys.argv[4])   if len(sys.argv) > 4 else 300
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
    print("R=%.2f NTHETA=%d primes<=%d (%d) prec=%d  [s = 1 fixed]"
          % (R, NTHETA, PCUT, len(primes), PREC), flush=True)

    # tail bounds for p > PCUT, using s = 1 so p^-s = 1/p.
    #   L   terms: |z log(1-1/p) - log(1-z/p)| <= |z|(|z|+1)/p^2 * 1.1
    #   L'  terms: carry an extra log p     -> sum_{p>P} log p/p^2 <= 2.52/P
    #   L'' terms: carry (log p)^2          -> sum_{p>P} (log p)^2/p^2
    #                                          <= 2.52 (log P + 1)/P
    P = arb(PCUT)
    zmag = arb(R)
    fac = zmag * (zmag + 1) * arb("1.1")
    tailL  = arb(4) * zmag / (P * P.log())
    tailL1 = fac * arb("2.52") / P
    tailL2 = fac * arb("2.52") * (P.log() + 1) / P
    print("tail bounds:  L %.3e   L' %.3e   L'' %.3e"
          % (float(tailL), float(tailL1), float(tailL2)), flush=True)

    one = acb(1)
    worst = [arb(0), arb(0), arb(0)]

    for i in range(NTHETA):
        th = interval(arb(2) * arb.pi() * i / NTHETA,
                      arb(2) * arb.pi() * (i + 1) / NTHETA)
        z = acb(th.cos(), th.sin()) * R

        reL = arb(0)          # Re(L), real
        L1 = acb(0)           # L'
        L2 = acb(0)           # L''

        for base in (2, 3):
            a = arb(1) / arb(base)          # base^-1, s = 1
            la = arb(base).log()
            reL += (z * acb((1 - a).log())).real
            L1 += z * acb(a * la / (1 - a))
            L2 += z * acb(-la * la * a / ((1 - a) * (1 - a)))

        for p in primes:
            ap = arb(1) / arb(p)
            lp = arb(p).log()
            zap = z * acb(ap)
            den = one - zap                 # 1 - z p^-s
            reL += (z * acb((1 - ap).log())).real
            reL -= abs(den).log()
            L1 += z * acb(lp * ap / (1 - ap)) - z * acb(lp * ap) / den
            L2 += (z * acb(-lp * lp * ap / ((1 - ap) * (1 - ap)))
                   + z * acb(lp * lp * ap) / (den * den))

        reL += interval(-tailL, tailL)
        L1 += acb(interval(-tailL1, tailL1), interval(-tailL1, tailL1))
        L2 += acb(interval(-tailL2, tailL2), interval(-tailL2, tailL2))

        H = reL.exp()
        m0 = H
        m1 = H * abs(L1)
        m2 = H * (abs(L1) * abs(L1) + abs(L2))

        for j, m in enumerate((m0, m1, m2)):
            u = arb(float(m.upper()))
            if float(u) > float(worst[j]):
                worst[j] = u

        if (i + 1) % 50 == 0:
            print("  theta %d/%d  M0<=%.4f M1<=%.4f M2<=%.4f"
                  % (i + 1, NTHETA, float(worst[0]), float(worst[1]),
                     float(worst[2])), file=sys.stderr, flush=True)

    M0, M1, M2 = (float(w) for w in worst)
    print()
    print("M_0 <= %.6f" % M0)
    print("M_1 <= %.6f" % M1)
    print("M_2 <= %.6f" % M2)
    print()

    # C in |R_k| <= C k^3 3^-k.
    #   |[z^i] d_s^2 H(1,z)| <= (M_2/(1-3/R)) * ((i+2)^2/2) * 3^-i
    #   order-3 term: 3^-(k+1) sum_{i<=k} |c_i^(3)| 3^i
    #                 <= 3^-(k+1) * (M_2/(1-3/R)) * sum_{i<=k}(i+2)^2/2
    #                 <= 3^-(k+1) * (M_2/(1-3/R)) * (k+3)^3/6
    geo = 1.0 / (1.0 - 3.0 / R)
    C = M2 * geo / 18.0            # (1/3) * (1/6)
    print("geometric factor 1/(1-3/R) = %.4f" % geo)
    print("C = M_2/(1-3/R)/18 = %.6f      [in |R_k| <= C (k+3)^3 3^-k]" % C)
    print()
    print("calibrated C from the certified f_k^odd was 0.0021;")
    print("this derived C is an upper bound and will be larger.")


if __name__ == "__main__":
    main()
