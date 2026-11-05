"""Decisive test of the boundary reduction, and of the cost of the freezing.

The reduction behind eq:boundary-reduction is

    f_k^P = sum_{m=1}^{k} phi_{k-m}(1) I_m  +  int_1^inf phi_k(s) ds  +  E_k,

the m = 0 term kept UNFROZEN because I_0 = int_1^inf 1 ds diverges.  The first
write-up claimed E_k = O(e^-k) = o(2^-k), on the ground that the mass of the
s-integral sits at s - 1 ~ e^-k.  That is wrong: the Jensen error is governed
by the first moment K_m = int (s-1)[I_m integrand] ds, which is Theta(m 2^-m).

This script measures E_k directly.  The left side is computed INDEPENDENTLY of
the Phi decomposition, from f_k^P = int_1^inf P_k^P(s) ds with
P_k^P(s) = sum_j h_j(s) u^{k-j}/(k-j)!, h_j = [z^j] H_P -- the route
boundary_check.py uses -- so the two sides share no code path.

Test case: Q = {3}, i.e. P = all primes except 3, so q = 2 (the boundary case)
and Phi_P = H_{P minus {2}} is the regularized product over {p >= 5}.

Result (log in freeze.log).  Two things come out:

  * Phi_P(1,1) = 0.33333334 against prod_{p in Q}(1-1/p) = 1/3, confirming the
    DERIVED centring constant that the boundary numerics had been assuming by
    analogy.
  * residual/2^-k = 2.00, 1.12, 1.09, 1.24 at k = 6, 8, 10, 12.  It does not
    tend to 0, so E_k is NOT o(2^-k) and the original claim is refuted
    numerically as well as analytically.  It is consistent with the corrected
    E_k = O(k 2^-k), and the reduction is accurate to o(k^2 2^-k) -- which is
    all Conjecture 7.1 needs, since its sign is decided at order k^2 2^-k.

mpmath, not Arb: no certificate, and nothing in the paper or the formalization
depends on it.

    python3 boundary_freeze_check.py 6,8,10,12       # settings of record
"""
import sys
from mpmath import mp, mpf, exp, log, zeta, primezeta, quad, factorial, inf

KS = [int(x) for x in (sys.argv[1] if len(sys.argv) > 1 else "8,10,12,14").split(',')]
PR = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
QSET = [3]                 # complement of P
DROP_PHI = [2, 3]          # complement of P \ {2}


def Am(m, s, drop):
    t = mpf(m) * s
    v = primezeta(t) if t < 21 else sum(mpf(p) ** (-t) for p in PR)
    return v - sum(mpf(p) ** (-t) for p in drop)


def hco(s, K, drop, MSER=90):
    """[z^i] H_{primes minus drop}(s,z), i <= K."""
    c = [mp.zero] * (K + 1)
    if K >= 1:
        c[1] += sum(log(1 - mpf(p) ** (-s)) for p in drop)
    for m in range(2, MSER + 1):
        a = Am(m, s, drop)
        if K >= 1:
            c[1] -= a / m
        if m <= K:
            c[m] += a / m
    h = [mp.zero] * (K + 1); h[0] = exp(c[0])
    for n in range(1, K + 1):
        acc = mp.zero
        for j in range(1, n + 1):
            acc += j * c[j] * h[n - j]
        h[n] = acc / n
    return h


def dps_for(k):
    return int(40 + 0.45 * (k + 14 * (k + 1) ** 0.5)) + 15


def fk_direct(k):
    """f_k^P from H_P directly -- no Phi decomposition anywhere."""
    mp.dps = dps_for(k)

    def integ(t):
        x = exp(-t); s = 1 + x
        u = log(zeta(s))
        h = hco(s, k, QSET)
        tot = mp.zero
        for j in range(0, k + 1):
            tot += h[j] * u ** (k - j) / factorial(k - j)
        return tot * x

    w = mp.sqrt(k + 1)
    return quad(integ, [max(mpf(k) - 12 * w, mpf(-2)), mpf(k), mpf(k) + 14 * w],
                maxdegree=5)


def I(m):
    """int_1^inf 2^{-ms} sum_{j<=m}(2^s u)^j/j! ds, finite for m >= 1."""
    mp.dps = dps_for(m) if m >= 6 else 40

    def integ(t):
        x = exp(-t); s = 1 + x
        y = mpf(2) ** s * log(zeta(s))
        tot = mp.zero; term = mp.one
        for j in range(0, m + 1):
            if j: term = term * y / j
            tot += term
        return mpf(2) ** (-m * s) * tot * x

    w = mp.sqrt(m + 1)
    return quad(integ, [max(mpf(m) - 12 * w, mpf(-2)), mpf(m), mpf(m) + 14 * w],
                maxdegree=5)


def phi_tail_integral(k):
    """int_1^inf phi_k(s) ds, the unfrozen m=0 term."""
    mp.dps = 40
    f = lambda s: hco(s, k, DROP_PHI)[k]
    return quad(f, [1, mpf('1.2'), 2, 5, 20, inf])


KMAX = max(KS)
print("Q =", QSET, " (q = 2, boundary case);  Phi_P = H for {p>=5}")
mp.dps = 50
phi1 = hco(mpf(1), KMAX, DROP_PHI)
print("Phi_P(1,1) = sum_i phi_i(1) =", mp.nstr(sum(phi1), 14),
      "   prod_{p in {2,3}}(1-1/p) =", mp.nstr(mpf(1) / 3, 14))
print("Phi_P(1,2) = sum_i phi_i(1)2^i =",
      mp.nstr(sum(phi1[i] * mpf(2) ** i for i in range(KMAX + 1)), 14))
print()
Ic = {m: I(m) for m in range(1, KMAX + 1)}
print(" k   f_k^P (direct)        reconstruction        residual      residual/2^-k")
for k in KS:
    mp.dps = 50
    ph = hco(mpf(1), k, DROP_PHI)
    rec = sum(ph[k - m] * Ic[m] for m in range(1, k + 1)) + phi_tail_integral(k)
    direct = fk_direct(k)
    res = direct - rec
    print("%3d  %s  %s  %s  %s" % (
        k, mp.nstr(direct, 16), mp.nstr(rec, 16), mp.nstr(res, 8),
        mp.nstr(res / mpf(2) ** (-k), 8)))
    sys.stdout.flush()
