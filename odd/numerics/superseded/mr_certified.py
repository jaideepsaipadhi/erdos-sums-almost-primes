#!/usr/bin/env python3
"""Certified M_R = sup_{|z|=R, s in [1,2]} |Htilde(s,z)| -- the last quantity
the odd theorem needs.

    Htilde(s,z) = (1-2^-s)^z (1-3^-s)^z prod_{p>=5} (1-z p^-s)^-1 (1-p^-s)^z

analytic in |z| < 5^s, so Cauchy on |z| = R < 5 bounds the Taylor coefficients
by M_R R^-k, which dominates the remainder in

    f_k^odd = 1/2 + beta 2^-k + R_k,   beta = 0.15563271

Usage: python3 mr_certified.py R NTHETA PCUT PREC
"""
import sys
from flint import arb, acb, ctx
R      = float(sys.argv[1]) if len(sys.argv) > 1 else 4.5
NTHETA = int(sys.argv[2])   if len(sys.argv) > 2 else 200
PCUT   = int(sys.argv[3])   if len(sys.argv) > 3 else 100000
PREC   = int(sys.argv[4])   if len(sys.argv) > 4 else 200
ctx.prec = PREC

def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(5, n + 1) if s[i]]

def interval(lo, hi):
    return ((lo + hi) / 2).union(lo).union(hi)

def main():
    primes = sieve(PCUT)
    print("R=%.2f NTHETA=%d primes<=%d (%d) prec=%d"
          % (R, NTHETA, PCUT, len(primes), PREC), flush=True)
    NS = 40
    worst = arb(0)
    for si in range(NS):
      sbox = interval(arb(1) + arb(si) / NS, arb(1) + arb(si + 1) / NS)
      for i in range(NTHETA):
          th = interval(arb(2) * arb.pi() * i / NTHETA,
                        arb(2) * arb.pi() * (i + 1) / NTHETA)
          z = acb(th.cos(), th.sin()) * R
          acc = arb(0)
          for base in (2, 3):
              t = (1 - arb(base) ** (-sbox)).log()
              acc += (z * acb(t)).real
          for p in primes:
              pw = arb(p) ** (-sbox)
              acc += (z * acb((1 - pw).log())).real
              acc -= abs(acb(1) - z * acb(pw)).log()
          tail = arb(4) * arb(R) / (arb(PCUT) * arb(PCUT).log())
          acc += interval(-tail, tail)
          u = arb(float(acc.exp().upper()))
          if float(u) > float(worst):
              worst = u
          if (i + 1) % 50 == 0:
              print("  theta box %d/%d, running sup %.4f"
                    % (i + 1, NTHETA, float(worst)), file=sys.stderr, flush=True)
    print("M_R <= %s" % worst.str(12))

if __name__ == "__main__":
    main()
