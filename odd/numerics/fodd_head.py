#!/usr/bin/env python3
"""Head computation of f_k^odd = sum_{Omega(n)=k, n odd} 1/(n log n).

Direct enumeration to N.  Only a head -- the smallest odd n with Omega(n) = k
is 3^k, so this is reliable only while 3^k << N.  Enough to see the trend and
to check any later certified computation against.

Usage: python3 fodd_head.py [N] [KMAX]
"""
import sys, math

def main(N=10**7, KMAX=14):
    spf = list(range(N + 1))
    i = 2
    while i * i <= N:
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1

    def omega(n):
        c = 0
        while n > 1:
            n //= spf[n]
            c += 1
        return c

    f = {}
    for n in range(3, N + 1, 2):
        k = omega(n)
        if k <= KMAX:
            f[k] = f.get(k, 0.0) + 1.0 / (n * math.log(n))

    print("N = %d   (head is reliable while 3^k << N, i.e. k <~ %d)"
          % (N, int(math.log(N) / math.log(3))))
    print(" k   f_k^odd (head)      ratio")
    prev = None
    for k in sorted(f):
        r = (f[k] / prev) if prev else float("nan")
        print("%2d   %.10f        %.4f" % (k, f[k], r))
        prev = f[k]

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    main(N, K)
