#!/usr/bin/env python3
"""The first moment K_m behind eq:freeze-error.

K_m is the one quantity the boundary reduction's error estimate rests on, and
until this script existed its four numerals lived only in the DOCSTRINGS of
Im_check.py and boundary_freeze_check.py -- nothing in the repository computed
them.  Im_check.py computes I_m, not K_m; boundary_freeze_check.py measures
E_k directly and never forms K_m.  That is the same provenance defect the
criterion certificates had, so:

    K_m = int_1^inf (s - 1) 2^{-ms} sum_{j<=m} (2^s log zeta(s))^j / j!  ds,

the (s-1)-weighted version of I_m.  Freezing phi_i at s = 1 inside the
s-integral is a Jensen step, and K_m is the weight its first-order error
carries: E_k = sum_i phi_i'(1) K_{k-i} + (Taylor remainder).

The point of the computation is NEGATIVE: it refutes the first write-up's
claim that the freezing costs O(e^-k).  The mass of the integrand does sit at
s - 1 ~ e^-m, but the expectation of s-1 is not e^{-E t}, and

    K_m 2^m / m   ->   a constant of order 0.4,

so K_m is of order m 2^-m, which is larger than e^-m by six orders of
magnitude already at m = 36.  The column drifts upward over the range
computed and does not flatten, so an extra slowly varying factor (log m, say)
is not excluded by this data; the paper states the conclusion in a form that
does not depend on which it is, since m 2^-m and m log m 2^-m are both
o(m^2 2^-m), and that is all the reduction needs.

Also printed: the second moment ratio, so the Taylor remainder of
eq:freeze-error can be seen to be smaller by a factor ~ 2^-m.

mpmath, not Arb: no certificate, and nothing in the formalization depends on
it.  Working precision must grow with m -- s = 1 + e^-t rounds to exactly 1 at
the top of the t-range otherwise, and zeta is then evaluated at its pole.

    python3 km_check.py                 # settings of record -> km.log
    python3 km_check.py 16,24,32,36 5
"""
import sys
from mpmath import mp, mpf, exp, log, zeta, quad

ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
MS = [int(x) for x in (ARGS[0] if ARGS else "8,12,16,20,24,28,32,36").split(',')]
DEG = int(ARGS[1]) if len(ARGS) > 1 else 5


def dps_for(m):
    return int(40 + 0.45 * (m + 14 * (m + 1) ** 0.5)) + 10


def moment(m, power):
    """int_1^inf (s-1)^power 2^{-ms} sum_{j<=m}(2^s log zeta(s))^j/j! ds."""
    mp.dps = dps_for(m)

    def integ(t):
        x = exp(-t)                      # = s - 1
        s = 1 + x
        y = mpf(2) ** s * log(zeta(s))
        tot = mp.zero
        term = mp.one
        for j in range(0, m + 1):
            if j:
                term = term * y / j
            tot += term
        return x ** power * mpf(2) ** (-m * s) * tot * x

    w = mp.sqrt(m + 1)
    lo = max(mpf(m) - 12 * w, mpf(-2))
    hi = mpf(m) + 14 * w
    return quad(integ, [lo, mpf(m), hi], maxdegree=DEG)


print("== the first moment K_m, and what it refutes ==")
print("   claimed in the first write-up:  freezing error = O(e^-k)")
print("   actual:                         K_m of order m 2^-m")
print()
print("%4s  %22s  %16s  %14s  %16s"
      % ("m", "K_m", "K_m 2^m / m", "e^-m / K_m", "K2_m / K_m 2^-m"))
for m in MS:
    K = moment(m, 1)
    K2 = moment(m, 2)
    print("%4d  %22s  %16s  %14s  %16s"
          % (m, mp.nstr(K, 16), mp.nstr(K / (mpf(m) * mpf(2) ** (-m)), 10),
             mp.nstr(exp(-mpf(m)) / K, 6),
             mp.nstr(K2 / (K * mpf(2) ** (-m)), 8)))
    sys.stdout.flush()

print()
print("K_m 2^m / m rises over this range without flattening, so the data fix the")
print("order as m 2^-m only up to a slowly varying factor.  Either way K_m is")
print("Theta(m 2^-m) at worst a log off, hence o(m^2 2^-m), which is what the")
print("reduction needs, and hugely larger than e^-m.  The last column shows the")
print("second moment is smaller by a factor ~2^-m, so the Taylor remainder of")
print("eq:freeze-error does not disturb the order.")
