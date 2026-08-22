#!/usr/bin/env python3
"""f_k^odd via the integral representation, using the p >= 3 Euler product.

    f_k^odd = int_1^inf [z^k] prod_{p>=3} (1 - z p^-s)^-1 ds

The coefficients come from the standard exp-of-log recursion:
    log prod = sum_{j>=1} P_odd(js) z^j / j,   P_odd(t) = sum_{p>=3} p^-t
    c_0 = 1,  c_n = (1/n) sum_{j=1}^n j l_j c_{n-j}

This is the odd analogue of ci_certified.py's recursion, and unlike the head
enumeration it is valid for every k.  Floating point here -- the certified
version comes later.

Usage: python3 fodd_series.py [KMAX] [PCUT]
"""
import sys, math
from mpmath import mp, mpf, quad, log

def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n + 1) if s[i]]

def coeffs(s, N, primes):
    l = [mpf(0)] * (N + 1)
    for j in range(1, N + 1):
        t = mpf(0)
        for p in primes:
            t += mpf(p) ** (-mpf(j) * s)
        l[j] = t / j
    c = [mpf(1)]
    for n in range(1, N + 1):
        acc = mpf(0)
        for j in range(1, n + 1):
            acc += j * l[j] * c[n - j]
        c.append(acc / n)
    return c

def main(KMAX=12, PCUT=50000):
    mp.dps = 25
    primes = primes_upto(PCUT)
    print("primes to %d (%d of them), KMAX=%d" % (PCUT, len(primes), KMAX))
    print(" k   f_k^odd              ratio")
    prev = None
    for k in range(1, KMAX + 1):
        v = quad(lambda t: coeffs(1 + t, k, primes)[k], [0, 0.25, 1, 4, 16])
        r = (v / prev) if prev else mpf("nan")
        print("%2d   %.12f       %.5f" % (k, float(v), float(r)))
        prev = v

if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    P = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
    main(K, P)
