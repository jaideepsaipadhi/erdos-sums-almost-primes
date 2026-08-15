#!/usr/bin/env python3
"""Certified h_i^(r)(s) = [z^i] d_s^r H(s,z) for r = 0,1,2 and i <= NMAX,
computed by DIRECT INTERVAL RECURSION rather than by a Cauchy estimate on a
circle.

This is the odd analogue of the main development's beta_sweep.py, and it exists
for the same reason: a Cauchy bound on |z| = R is dominated by the maximum over
the circle and discards the cancellation among the true coefficients.  For the
odd case that loss is a factor of about 1.6e8, which pushes K0 past 70; the
direct recursion is what the main development used to recover two orders of
magnitude (see numerics/superseded/K0-proof-v7.md section 8, item 2).

STRUCTURE.

    H(s,z) = (1-2^-s)^z prod_{p>=3} (1 - z p^-s)^-1 (1-p^-s)^z

    log H(s,z) = z L_1(s) + sum_{j>=2} z^j L_j(s),
      L_1(s) = log(1-2^-s) + sum_{p>=3} [ p^-s + log(1-p^-s) ]
      L_j(s) = P(s,j)/j,   P(s,j) = sum_{p>=3} p^-sj      (j >= 2)

    L_1'  = log2/(2^s-1) + sum_{p>=3} log p / (p^s (p^s - 1))
    L_j'  = -sum_{p>=3} log p * p^-sj                      (j >= 2)
    L_1'' = -log2^2 2^s/(2^s-1)^2
            + sum_{p>=3} (1-2p^s)(log p)^2 / (p^s (p^s-1)^2)
    L_j'' = sum_{p>=3} j (log p)^2 p^-sj                   (j >= 2)

Coefficients of H by the exp recurrence:
    h_0 = 1,   h_m = (1/m) sum_{j=1}^{m} j L_j h_{m-j}

Then with D_r = sum_j L_j^(r) z^j,
    d_s   H = H D_1          -> [z^i] = sum_m h_m (D_1)_{i-m}
    d_s^2 H = H (D_1^2 + D_2)-> [z^i] = sum_m h_m (D_1^2 + D_2)_{i-m}

Usage: python3 hcoeff_recursion.py [NMAX] [NS] [PCUT] [PREC]
"""
import sys
from flint import arb, ctx

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
NS   = int(sys.argv[2]) if len(sys.argv) > 2 else 40
PCUT = int(sys.argv[3]) if len(sys.argv) > 3 else 100000
PREC = int(sys.argv[4]) if len(sys.argv) > 4 else 300
ctx.prec = PREC


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n + 1) if s[i]]


def interval(lo, hi):
    return ((lo + hi) / 2).union(lo).union(hi)


def conv(a, b, n):
    """(a*b)_i for i <= n, from lists a, b indexed 0..n."""
    out = [arb(0)] * (n + 1)
    for i in range(n + 1):
        acc = arb(0)
        for m in range(i + 1):
            acc += a[m] * b[i - m]
        out[i] = acc
    return out


def main():
    primes = sieve(PCUT)
    print("NMAX=%d NS=%d primes<=%d (%d) prec=%d"
          % (NMAX, NS, PCUT, len(primes), PREC), flush=True)

    P = arb(PCUT)
    # tails for p > PCUT at s >= 1:
    #   sum p^-j       <= 1/((j-1) P^(j-1) log P)     (j >= 2)
    #   sum log p p^-j <= (log P + 1)/((j-1) P^(j-1))
    #   sum log^2 p p^-j <= (log P + 1)^2/((j-1) P^(j-1))
    def tails(j):
        if j == 1:
            t0 = arb(2) / (P * P.log())
            t1 = (P.log() + 1) * 2 / P
            t2 = (P.log() + 1) ** 2 * 2 / P
        else:
            d = arb(j - 1) * P ** (j - 1)
            t0 = arb(1) / (d * P.log())
            t1 = (P.log() + 1) / d
            t2 = (P.log() + 1) ** 2 / d
        return t0, t1, t2

    worst = [[arb(0)] * (NMAX + 1) for _ in range(3)]
    Sworst = [arb(0)]

    for si in range(NS):
        sbox = interval(arb(1) + arb(si) / NS, arb(1) + arb(si + 1) / NS)
        pw = [(arb(p) ** sbox, arb(p).log()) for p in primes]   # p^s, log p

        L  = [arb(0)] * (NMAX + 1)
        L1 = [arb(0)] * (NMAX + 1)
        L2 = [arb(0)] * (NMAX + 1)

        # j = 1
        a2 = arb(2) ** sbox
        l2 = arb(2).log()
        acc  = (1 - 1 / a2).log()
        acc1 = l2 / (a2 - 1)
        acc2 = -l2 * l2 * a2 / ((a2 - 1) * (a2 - 1))
        for ps, lp in pw:
            acc  += 1 / ps + (1 - 1 / ps).log()
            acc1 += lp / (ps * (ps - 1))
            acc2 += (1 - 2 * ps) * lp * lp / (ps * (ps - 1) * (ps - 1))
        t0, t1, t2 = tails(1)
        L[1]  = acc  + interval(-t0, t0)
        L1[1] = acc1 + interval(-t1, t1)
        L2[1] = acc2 + interval(-t2, t2)

        # j >= 2   (qcur holds p^-s(j-1), updated in place)
        qcur = [arb(1) / ps for ps, _ in pw]
        for j in range(2, NMAX + 1):
            acc = acc1 = acc2 = arb(0)
            for t in range(len(pw)):
                ps, lp = pw[t]
                qcur[t] = qcur[t] / ps
                q = qcur[t]
                acc  += q
                acc1 += lp * q
                acc2 += lp * lp * q
            t0, t1, t2 = tails(j)
            L[j]  = acc / j + interval(-t0, t0)
            L1[j] = -(acc1 + interval(-t1, t1))
            L2[j] = j * (acc2 + interval(-t2, t2))

        # h_m by the exp recurrence
        h = [arb(0)] * (NMAX + 1)
        h[0] = arb(1)
        for m in range(1, NMAX + 1):
            acc = arb(0)
            for j in range(1, m + 1):
                acc += arb(j) * L[j] * h[m - j]
            h[m] = acc / m

        d1 = conv(h, L1, NMAX)                       # [z^i] d_s H
        L1sq = conv(L1, L1, NMAX)
        mid = [L1sq[i] + L2[i] for i in range(NMAX + 1)]
        d2 = conv(h, mid, NMAX)                      # [z^i] d_s^2 H

        for r, arr in enumerate((h, d1, d2)):
            for i in range(NMAX + 1):
                u = arb(float(abs(arr[i]).upper()))
                if float(u) > float(worst[r][i]):
                    worst[r][i] = u

        # G_2 = d_s^2 H * (1 - z/3)^3 = d_s^2 H * (1 - z + z^2/3 - z^3/27).
        # Formed INSIDE the box so the alternating cancellation survives;
        # taking sups first would destroy it.
        Sbox = arb(0)
        for j in range(NMAX + 1):
            g = d2[j]
            if j >= 1: g = g - d2[j-1]
            if j >= 2: g = g + d2[j-2] / 3
            if j >= 3: g = g - d2[j-3] / 27
            Sbox += abs(g) * arb(3) ** j
        if float(Sbox.upper()) > float(Sworst[0]):
            Sworst[0] = arb(float(Sbox.upper()))

        print("  s box %d/%d" % (si + 1, NS), file=sys.stderr, flush=True)

    print()
    print("sup over s in [1,2] of |[z^i] d_s^r H(s,z)|, and the ratio to 3^-i:")
    print("%4s %14s %14s %14s   %10s" % ("i", "r=0", "r=1", "r=2", "|h''|3^i/i^2"))
    for i in range(1, NMAX + 1):
        v = [float(worst[r][i]) for r in range(3)]
        sc = v[2] * 3.0 ** i / (i * i)
        print("%4d %14.6e %14.6e %14.6e   %10.4f" % (i, v[0], v[1], v[2], sc))

    # G_2 = d_s^2 H * (1 - z/3)^3, whose coefficients decay like R^-j for R < 5.
    # S = sum_j |g_j| 3^j is what the tail sum needs, and the head captures it.
    print()
    print("G_2 = d_s^2 H (1-z/3)^3 :  g_j and the running S = sum |g_j| 3^j")
    S = 0.0
    for j in range(NMAX + 1):
        g = float(worst[2][j])
        if j >= 1: g -= float(worst[2][j-1])
        if j >= 2: g += float(worst[2][j-2]) / 3.0
        if j >= 3: g -= float(worst[2][j-3]) / 27.0
        S += abs(g) * 3.0 ** j
        print("  j=%2d  g_j=%12.5e   |g_j|3^j=%12.5e   S=%12.5e"
              % (j, g, abs(g) * 3.0 ** j, S))
    print()
    print("S (head, j <= %d) = %.4f" % (NMAX, S))
    print("C_2 ~ S/6 = %.4f" % (S / 6))

    S = float(Sworst[0])
    print()
    print("S = sup_s sum_{j<=%d} |g_j| 3^j = %.6f" % (NMAX, S))
    print("   (g_j are G_2's coefficients; they decay like R^-j, R<5,")
    print("    so the head captures nearly all of S)")
    Cs = S / 6.0
    print("C = S/6 = %.6f   [in |R_k| <= C (k+3)^3 3^-k]" % Cs)
    beta_ = 0.15563271
    thr_ = beta_ / 3 / Cs
    K0s = None
    for k in range(5, 400):
        v = (k + 3) ** 3 * (2 / 3) ** k
        if v < thr_ and K0s is None: K0s = k
        elif v >= thr_: K0s = None
    print("K0 from S = %s" % K0s)

    C2 = max(float(worst[2][i]) * 3.0 ** i / (i * i) for i in range(1, NMAX + 1))
    print()
    print("C_2 = max_i |h_i''| 3^i / i^2 = %.4f" % C2)
    C = C2 / 18.0
    print("C = C_2/18 = %.6f   [in |R_k| <= C (k+3)^3 3^-k]" % C)
    beta = 0.15563271
    thr = beta / 3 / C
    K0 = None
    for k in range(5, 400):
        v = (k + 3) ** 3 * (2 / 3) ** k
        if v < thr and K0 is None:
            K0 = k
        elif v >= thr:
            K0 = None
    print("K0 = %s" % K0)
    print()
    print("NOTE: C_2 here is a max over i <= NMAX.  Extending it to all i needs")
    print("a tail argument -- the Cauchy bound on the pole-free part supplies")
    print("one, and is only needed for i > NMAX where it is far less lossy.")


if __name__ == "__main__":
    main()
