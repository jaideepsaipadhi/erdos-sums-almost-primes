"""Boundary case q = 2: is the leading coefficient proportional to the value of
the analytic factor at the critical point (s,z) = (1,2)?

H_P(s,z) = H_all(s,z) * E_Q(s,z),   E_Q(s,z) = prod_{p in Q} (1 - z p^-s),

so if the leading coefficient depends on the analytic factor only through its
VALUE at (1,2), then

    (f_k^P - c_0^P) / (f_k^all - 1)  ->  E_Q(1,2) = prod_{p in Q} (1 - 2/p),

with c_0^P = H_P(1,1) = prod_{p in Q}(1 - 1/p).  Since q = 2 forces 2 notin Q,
every factor of E_Q(1,2) is positive, so a confirmed limit here makes
non-cancellation for general P a consequence of the all-primes case.

Method.  f_k = int_1^inf P_k(s) ds with P_k(s) = sum_j h_j(s) u^(k-j)/(k-j)!,
u = log zeta(s), and h_j = [z^j] H_P(s,z) from

    log H_P(s,z) = sum_{m>=2} (z^m - z)/m * A_m(s) + z * B(s),
    A_m(s) = primezeta(ms) - sum_{p in Q} p^-ms,
    B(s)   = sum_{p in Q} log(1 - p^-s).

Substituting s = 1 + e^-t puts the mass of the integrand at t ~ k with width
~sqrt(k), so no inversion of zeta is needed anywhere.

What it shows, and what it does not.  This is EVIDENCE, not a proof: it tests
a consequence of the reduction, namely that the ratio has the predicted limit.
It cannot distinguish "the coefficient depends only on the value at (1,2)" from
"the s-derivative terms happen to cancel for this Q".  A second complement is
run for that reason.

Settings of record (boundary.log):

    python3 boundary_check.py 44 3 4 24,28,32,36,40,44
    python3 boundary_check.py 44 5 4 24,28,32,36,40,44

The ratio approaches the prediction from below with a 1/k correction, so read
the two-term extrapolation, not the raw k=44 value: for Q={3} the raw ratio is
0.31209 against 1/3, while the (L + a/k + b/k^2) fit through k=36,40,44 gives
0.3332266 -- a relative error of 3.2e-4.  k below about 20 is useless here; the
subleading terms still dominate.

`maxdegree` is mpmath's quadrature depth, not a precision in digits; degree 4
and 5 agree to 6 digits on f_k.  Working precision is set from k by dps_for,
because the substitution forms 1 + e^-t and that rounds to 1 at the top of the
t-range unless dps exceeds ~0.45*t.

Usage:  python3 boundary_check.py KMAX [complement] [maxdegree] [k-list]
"""
import sys
from mpmath import mp, mpf, exp, log, zeta, primezeta, quad, factorial

mp.dps = 30

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 24
QSET = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 and sys.argv[2] else []
MSER = max(48, KMAX + 2)

_pz = {}
_SMALLP = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def pz(m, s):
    """sum_p p^-(ms), memoized; both quadrature passes hit identical nodes.

    For ms >= 21 the sum over p <= 47 is already exact to ~1e-37, so primezeta
    (the expensive branch) is only called where it is actually needed."""
    key = (m, mp.nstr(s, mp.dps + 5))
    v = _pz.get(key)
    if v is None:
        t = mpf(m) * s
        v = primezeta(t) if t < 21 else sum(mpf(p) ** (-t) for p in _SMALLP)
        _pz[key] = v
    return v


def hcoeffs(s, K, Q):
    c = [mp.zero] * (K + 1)
    if K >= 1:
        c[1] += sum(log(1 - mpf(p) ** (-s)) for p in Q)
    for m in range(2, MSER + 1):
        Am = pz(m, s) - sum(mpf(p) ** (-mpf(m) * s) for p in Q)
        if K >= 1:
            c[1] -= Am / m
        if m <= K:
            c[m] += Am / m
    h = [mp.zero] * (K + 1)
    h[0] = exp(c[0])
    for n in range(1, K + 1):
        acc = mp.zero
        for j in range(1, n + 1):
            acc += j * c[j] * h[n - j]
        h[n] = acc / n
    return h


DEG = int(sys.argv[3]) if len(sys.argv) > 3 else 4


def fk(k, Q):
    """f_k^P via s = 1 + e^-t."""
    def integ(t):
        x = exp(-t)
        s = 1 + x
        u = log(zeta(s))
        h = hcoeffs(s, k, Q)
        tot = mp.zero
        for j in range(0, k + 1):
            tot += h[j] * u ** (k - j) / factorial(k - j)
        return tot * x

    w = mp.sqrt(k + 1)
    lo = max(mpf(k) - 11 * w, mpf(-5))
    hi = mpf(k) + 12 * w
    return quad(integ, [lo, mpf(k), hi], maxdegree=DEG)


def dps_for(k):
    """1 + e^-t must keep ~30 digits of e^-t at the top of the range."""
    hi = k + 12 * (k + 1) ** 0.5
    return int(30 + 0.45 * hi) + 5


c0_Q = mp.fprod([1 - mpf(1) / p for p in QSET]) if QSET else mpf(1)
E12 = mp.fprod([1 - mpf(2) / p for p in QSET]) if QSET else mpf(1)

print("complement Q =", QSET if QSET else "{} (all primes)")
print("c_0 = prod(1-1/p)                     =", mp.nstr(c0_Q, 20))
print("predicted ratio E_Q(1,2) = prod(1-2/p) =", mp.nstr(E12, 20))
print()
print("  k     f_k^all - 1        f_k^P - c_0         ratio")
rows = []
KLIST = ([int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4
         else list(range(8, KMAX + 1)))
for k in KLIST:
    mp.dps = dps_for(k)
    _pz.clear()
    c0k = mp.fprod([1 - mpf(1) / p for p in QSET]) if QSET else mpf(1)
    a = fk(k, []) - mpf(1)
    b = fk(k, QSET) - c0k
    r = b / a
    rows.append((mpf(k), r))
    print("%3d  %s  %s  %s" % (k, mp.nstr(a, 12), mp.nstr(b, 12), mp.nstr(r, 14)))
    sys.stdout.flush()

print()
print("deviation from the prediction, scaled by k (should tend to a constant")
print("if the ratio approaches E_Q(1,2) with a 1/k correction):")
for k, r in rows:
    print("   k=%-4s  E_Q(1,2) - ratio = %-14s  k*(that) = %s"
          % (int(k), mp.nstr(E12 - r, 8), mp.nstr(k * (E12 - r), 8)))

if len(rows) >= 2:
    k1, r1 = rows[-2]
    k2, r2 = rows[-1]
    e1 = (k2 * r2 - k1 * r1) / (k2 - k1)
    print()
    print("ratio at k=%-4s                       : %s" % (int(k2), mp.nstr(r2, 16)))
    print("one-term  (L + a/k) extrapolation    : %s" % mp.nstr(e1, 16))

if len(rows) >= 3:
    # fit L + a/k + b/k^2 through the last three k
    (ka, ra), (kb, rb), (kc, rc) = rows[-3], rows[-2], rows[-1]
    xs = [1 / ka, 1 / kb, 1 / kc]
    ys = [ra, rb, rc]
    # Lagrange value at x = 0 gives L
    L = mp.zero
    for i in range(3):
        term = ys[i]
        for j in range(3):
            if i != j:
                term *= (0 - xs[j]) / (xs[i] - xs[j])
        L += term
    print("two-term  (L + a/k + b/k^2) extrapol.: %s" % mp.nstr(L, 16))
    print("predicted E_Q(1,2)                   : %s" % mp.nstr(E12, 16))
    print("relative error of the two-term fit   : %s" % mp.nstr(abs(L / E12 - 1), 8))
