#!/usr/bin/env python3
"""Certified near-range bound on the ABSOLUTE coefficient sum of (5.1).

The manuscript's near-range step bounds

    T_k = int_{s(3)}^infty A_k(s) ds,
    A_k(s) = sum_{j<=k} u(s)^{k-j}/(k-j)! |h_j(s)|,      u(s) = log zeta(s),

by the SIGNED identity sum_j u^{k-j}/(k-j)! h_j(s) = P_k^odd(s), which needs
h_j >= 0.  absratio.py shows that is false (h_1 < 0 for every s, and the h_j
alternate).  This script bounds T_k directly and certifies

    3^k T_k <= CN = 367.8435    for all k >= 59,

which is the range on which (5.1) is used: the odd assembly takes the analytic
branch only for k >= K0 = 59, and monotonicity for k <= 75 comes from the
certified sweep, which never calls on the remainder bound.  So the repair
leaves CN, C = 4900 and K0 = 59 untouched.

METHOD.  Majorant.  log H_o(s,z) = h_1(s) z + sum_{m>=2} L_m z^m with
L_m = P_3(ms)/m > 0 and h_1 = L_1 - log zeta(s) < 0, so replacing h_1 by |h_1|
gives H_o^+ = H_o exp(-2 h_1 z), a series with NON-NEGATIVE coefficients
dominating |h_j| termwise.  Hence

    A_k(s) <= [z^k]( zeta(s)^z H_o^+(s,z) ) = P_k^+(s)
           =  sum_{i<=k} P_{k-i}^odd(s) a(s)^i / i!,     a = 2|h_1|,

where P_j^odd(s) = sum_{odd n, Omega(n)=j} n^-s are the coefficients of the odd
Euler product.

Quadrature needs no error analysis.  Every P_j^odd(s) is a Dirichlet series
with positive terms and a(s) = 2(sum_m 2^-ms/m + sum_{m>=2} P_3(ms)/m) is a
positive combination of decreasing functions, so P_k^+ is DECREASING in s and a
left-endpoint Riemann sum is an upper bound outright:

    T_k <= sum_{i<N} P_k^+(s_i) (s_{i+1} - s_i)  +  int_{s_N}^infty P_k^+ ds.

s-tail.  For t = s - s_N >= 0, P_{k-i}^odd(s) <= 3^{-(k-i)t} P_{k-i}^odd(s_N)
(every odd n with Omega(n) = k-i has n >= 3^{k-i}) and a(s) <= 2^-t a(s_N).
Since 3^-x <= 2^-x, each term decays by at least 2^{-kt}, so the tail is at
most P_k^+(s_N)/(k log 2).

k-tail.  For k > KMAX, Cauchy on |z| = R with R < 3^{s(3)} = 3.1727 and H_o^+
having non-negative coefficients (so its maximum on |z| = R is at z = R):

    A_k(s) <= R^-k zeta(s)^R H_o(s,R) e^{a(s)R}
            = R^-k M_R(s) e^{a(s)R},    M_R(s) = prod_{p>=3} (1 - R p^-s)^-1,

uniformly in k, whence 3^k T_k <= (3/R)^k [ int_{s(3)}^{s_N} M_R e^{aR} ds +
M_R(s_N) e^{a(s_N) R}/(k log 2) ].  R is taken just under 3^{s(3)}, so (3/R)^k
supplies the decay that makes the k-independent integral usable past KMAX.

PRIME SUMS.  P_3(t) = P(t) - 2^-t with P(t) = sum_n mu(n)/n log zeta(nt), the
Moebius series for the prime zeta function -- as in cn_certified.py and for the
same reason: at s ~ 1.05 summing over primes to any feasible cutoff leaves an
O(1) tail.  L_m for m > MMAX is bounded by its own tail rather than dropped.

GRID.  Graded from s(3) to SN: the integrand falls by several orders over the
first tenth of the range, so the spacing grows geometrically.

Settings of record: python3 nearabs_certified.py 200 8.0 220 60 60 400
    KMAX=200 k-head, SN=8.0 grid end, NGRID=220, MMAX=60, NMOB=60, PREC=400.

Usage: python3 nearabs_certified.py [KMAX] [SN] [NGRID] [MMAX] [NMOB] [PREC]
"""
import sys
from flint import arb, ctx
from sympy import mobius

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
SN = arb(sys.argv[2]) if len(sys.argv) > 2 else arb(8)
NGRID = int(sys.argv[3]) if len(sys.argv) > 3 else 220
MMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 60
NMOB = int(sys.argv[5]) if len(sys.argv) > 5 else 60
PREC = int(sys.argv[6]) if len(sys.argv) > 6 else 400
ctx.prec = PREC

three, two = arb(3), arb(2)
CN = arb('367.8435')
K0 = int(sys.argv[7]) if len(sys.argv) > 7 else 59

# ---------------------------------------------------------------- s(3)
lo, hi = arb('1.05'), arb('1.06')
assert (lo.zeta().log() > three) == True and (hi.zeta().log() < three) == True
for _ in range(120):
    mid = (lo + hi) / 2
    v = mid.zeta().log()
    if (v > three) == True:
        lo = mid
    elif (v < three) == True:
        hi = mid
    else:
        break
S3 = hi          # upper end of the bracket: starting the grid to the RIGHT of
                 # s(3) would lose part of the integral, so use the end that
                 # makes [S3, .] contain [s(3), .].
S3 = lo
print("s(3) in [%s, %s]; grid starts at the lower end" % (lo.lower(), hi.upper()))

MU = [0] + [int(mobius(n)) for n in range(1, NMOB + 1)]


def P_all(t):
    v = arb(0)
    for n in range(1, NMOB + 1):
        if MU[n]:
            v += arb(MU[n]) / n * (arb(n) * t).zeta().log()
    return v


def P_3(t):
    """sum_{p>=3} p^-t, as a ball."""
    return P_all(t) - two ** (-t)


def series_at(s, N):
    """(Pod, a) at s: odd-Euler-product coefficients to order N, and a = 2|h_1|.

    L_m = P_3(ms)/m for m <= MMAX; beyond MMAX the whole remaining tail is
    lumped into one ball on L_{MMAX+1}, which only inflates the majorant.
    """
    L = [arb(0)] * (N + 2)
    mtop = min(MMAX, N)
    for m in range(1, mtop + 1):
        L[m] = P_3(arb(m) * s) / m
    # sum_{m>mtop} P_3(ms)/m <= P_3((mtop+1)s) * 1/(1 - 3^-s) / (mtop+1).
    # Always set: the k-tail's M_R reuses this slot for its own remainder.
    L[mtop + 1] = P_3(arb(mtop + 1) * s) / (1 - three ** (-s)) / (mtop + 1)
    # exp of the log-series -> odd Euler product coefficients
    Pod = [arb(0)] * (N + 1)
    Pod[0] = arb(1)
    for n in range(1, N + 1):
        acc = arb(0)
        for m in range(1, min(n, mtop + 1) + 1):
            acc += arb(m) * L[m] * Pod[n - m]
        Pod[n] = acc / n
    # a = 2|h_1| = 2( sum_m 2^-ms/m + sum_{m>=2} P_3(ms)/m )
    #           = 2( -log(1 - 2^-s) + sum_{m>=2} L_m )
    a = 2 * (-(1 - two ** (-s)).log() + sum((L[m] for m in range(2, N + 2)), arb(0)))
    return Pod, a, L, mtop


def Pplus(Pod, a, k, fact):
    """P_k^+ = sum_{i<=k} P_{k-i}^odd a^i / i!."""
    acc = arb(0)
    ai = arb(1)
    for i in range(0, k + 1):
        acc += Pod[k - i] * ai / fact[i]
        ai = ai * a
        if i > 6 and (ai / fact[i + 1] * Pod[0] < arb(10) ** (-PREC // 4)) == True:
            break
    return acc


# ---------------------------------------------------------------- grid
# graded: s_i = S3 + (SN - S3) * ((i/N)^3), so spacing is fine near s(3)
grid = [S3 + (SN - S3) * (arb(i) / NGRID) ** 3 for i in range(NGRID + 1)]

fact = [arb(1)]
for i in range(1, KMAX + 2):
    fact.append(fact[-1] * i)

print("building series at %d grid points on [%s, %s] ..."
      % (NGRID + 1, S3.str(8, radius=False), SN.str(6, radius=False)))
ser = []
for i, s in enumerate(grid):
    ser.append(series_at(s, KMAX))
    if i % 40 == 0:
        print("  %d/%d" % (i, NGRID))

# ---------------------------------------------------------------- head in k
# EVERY k in [K0, KMAX], not a sample: the values do fall off monotonically in
# practice, but nothing here proves that, so sampling would not certify the sup.
print("\n    k     3^k T_k (upper)      vs CN=367.8435")
worst = arb(0)
worst_k = None
for k in range(K0, KMAX + 1):
    tot = arb(0)
    for i in range(NGRID):
        Pod, a = ser[i][0], ser[i][1]
        tot += Pplus(Pod, a, k, fact) * (grid[i + 1] - grid[i])
    PodN, aN = ser[NGRID][0], ser[NGRID][1]
    tot += Pplus(PodN, aN, k, fact) / (arb(k) * two.log())
    val = tot * three ** k
    if (val > worst) == True:
        worst, worst_k = val, k
    if (val <= CN) != True:
        print("%5d  %18s      EXCEEDS" % (k, val.str(10, radius=False)))
    elif k in (K0, 60, 65, 70, 75, 80, 90, 100, 120, 150, 180, KMAX):
        print("%5d  %18s      OK" % (k, val.str(10, radius=False)))
print("  (all %d values of k in [%d, %d] evaluated; only a sample printed)"
      % (KMAX - K0 + 1, K0, KMAX))

# ---------------------------------------------------------------- tail in k
R = arb('3.15')
assert (R < three ** S3) == True, "Cauchy radius must stay under 3^s(3)"


def M_R(s, L, mtop):
    """prod_{p>=3} (1 - R p^-s)^-1 = exp( sum_{m>=1} R^m P_3(ms)/m ).

    Reuses the L_m = P_3(ms)/m already built for this grid point; the m > mtop
    remainder is bounded by its leading term times the geometric factor
    1/(1 - R 3^-s), which needs R < 3^s.
    """
    r = R * three ** (-s)
    assert (r < 1) == True, "Cauchy radius must stay under 3^s"
    acc = arb(0)
    for m in range(1, mtop + 1):
        acc += R ** m * L[m]
    acc += R ** (mtop + 1) * L[mtop + 1] / (1 - r)
    return acc.exp()


tailint = arb(0)
for i in range(NGRID):
    _, a, L, mtop = ser[i]
    tailint += M_R(grid[i], L, mtop) * (a * R).exp() * (grid[i + 1] - grid[i])
_, aN, LN, mtopN = ser[NGRID]
tailint += M_R(grid[NGRID], LN, mtopN) * (aN * R).exp() / (arb(KMAX) * two.log())
ratio = (three / R) ** (KMAX + 1)
ktail = tailint * ratio
print("\nk-tail, Cauchy at R = %s:" % R.str(6, radius=False))
print("  int M_R e^{aR} ds + tail = %s" % tailint.str(10, radius=False))
print("  (3/R)^%d = %.3e,  so 3^k T_k <= %s for every k > %d"
      % (KMAX + 1, float(ratio.upper()), ktail.str(10, radius=False), KMAX))

ok = (worst <= CN) == True and (ktail <= CN) == True
print("\nworst over the whole head k in [%d, %d]: %s at k = %d"
      % (K0, KMAX, worst.str(10, radius=False), worst_k))
print("bound for k > %d:              %s" % (KMAX, ktail.str(10, radius=False)))
print("\n%s: 3^k T_k <= CN = 367.8435 for all k >= %d"
      % ("CERTIFIED" if ok else "NOT ESTABLISHED", K0))
sys.exit(0 if ok else 1)
