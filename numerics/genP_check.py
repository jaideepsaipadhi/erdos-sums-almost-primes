"""End-to-end test of the general-P constants of the paper's Section 7.

For a set of primes P with least element q and complement Q = primes \\ P
satisfying sum_{p in Q} (log p)/p < infinity, the claim under test is

    f_k^P = c_0 + c_2 2^-k + o(2^-k),      q >= 3  (interior case),
    c_0 = H_P(1,1) = prod_{p in Q} (1 - 1/p),
    c_2 = H_P(1,2) * ( gamma + (1/2) d_s log H_P(1,2) ),
    (1/2) d_s log H_P(1,2)
        = - sum_{p in P} log p/((p-1)(p-2)) + sum_{p in Q} log p/(p-1),

which is the constant asserted in Section 7, and which this script derives
independently from the factorization

    H_P(s,z) = prod_{p in P} L_p(s,z) * prod_{p in Q} (1 - p^-s)^z,
    L_p(s,z) = (1 - p^-s)^z (1 - z p^-s)^-1,
    log L_p  = sum_{m>=2} (z^m - z) p^-ms / m.

f_k^P itself is computed independently of all of that, from
f_k = int_1^inf P_k(s) ds with P_k(s) = sum_j h_j(s) u^(k-j)/(k-j)!,
u = log zeta(s), h_j = [z^j] H_P(s,z), under the substitution s = 1 + e^-t
(which puts the mass at t ~ k and needs no inversion of zeta).

Usage
    python3 genP_check.py Q_LIST K_LIST [maxdegree]

Settings of record (genP.log), three complements:

    python3 genP_check.py 2     10,14  4     # the odd case: c_2 must be beta
    python3 genP_check.py 2,3   10,14  4     # P = {p >= 5}
    python3 genP_check.py 2,5   10     4     # P = {3,7,11,...}, not an initial segment

The first is the calibration: P = {p >= 3} is the case the paper proves, so
c_2 there must reproduce the certified beta of (1.3) and H_P(1,2) the certified
d, which they do to ~1e-7 -- the width of the error bar carried by the p-sums
below, which are run to X = 2e6 with the PNT tail 1/X.  The product tail
prod_{p>X}(1-1/p)^2/(1-2/p) = 1 - O(1/(X log X)) is NOT included, and accounts
for the last reported digits of H_P(1,2) against d.

Beware: `maxdegree` is mpmath's quadrature depth, not a precision in digits.
Degree 4 and 5 agree to 6 digits on f_k; degree 3 does not.  The working
precision is set from k by dps_for, because the substitution forms 1 + e^-t and
at the top of the t-range that rounds to 1 unless dps exceeds ~0.45*t.
"""
import sys
from mpmath import mp, mpf, exp, log, zeta, primezeta, quad, factorial, euler

QSET = sorted(int(x) for x in sys.argv[1].split(',')) if len(sys.argv) > 1 else [2, 3]
KLIST = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [12, 16, 20, 24]
DEG = int(sys.argv[3]) if len(sys.argv) > 3 else 4

_pz = {}
_SMALLP = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def pz(m, s):
    """sum_p p^-(ms), memoized.  For ms >= 21 the sum over p <= 47 is already
    exact to ~1e-37, so primezeta (the expensive branch) is called only where
    it is needed."""
    key = (m, mp.nstr(s, mp.dps + 5))
    v = _pz.get(key)
    if v is None:
        t = mpf(m) * s
        v = primezeta(t) if t < 21 else sum(mpf(p) ** (-t) for p in _SMALLP)
        _pz[key] = v
    return v


def hcoeffs(s, K, Q, MSER):
    """[z^j] H_P(s,z) for j <= K."""
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


def fk(k, Q):
    MSER = max(48, k + 2)

    def integ(t):
        x = exp(-t)
        s = 1 + x
        u = log(zeta(s))
        h = hcoeffs(s, k, Q, MSER)
        tot = mp.zero
        for j in range(0, k + 1):
            tot += h[j] * u ** (k - j) / factorial(k - j)
        return tot * x

    w = mp.sqrt(k + 1)
    lo = max(mpf(k) - 11 * w, mpf(-5))
    hi = mpf(k) + 12 * w
    return quad(integ, [lo, mpf(k), hi], maxdegree=DEG)


def dps_for(k):
    return int(30 + 0.45 * (k + 12 * (k + 1) ** 0.5)) + 5


# ---------------------------------------------------------------- predictions
def primes_to(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b'\x00\x00'
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        i += 1
    return [i for i in range(2, n + 1) if sieve[i]]


def predicted(Q, X=2 * 10 ** 6):
    """c_0 and c_2 of the Section 7 formula.  The p-sums over P are run to X
    with the PNT tail sum_{p>X} log p/p^2 ~ 1/X added as an error bar."""
    mp.dps = 30
    allp = primes_to(X)
    P = [p for p in allp if p not in Q]
    q = P[0]
    c0 = mp.fprod([1 - mpf(1) / p for p in Q])
    # H_P(1,2) = prod_{p in P}(1-1/p)^2/(1-2/p) * prod_{p in Q}(1-1/p)^2
    hp = mp.fprod([(1 - mpf(1) / p) ** 2 / (1 - mpf(2) / p) for p in P])
    hp *= mp.fprod([(1 - mpf(1) / p) ** 2 for p in Q])
    SP = mp.fsum([log(mpf(p)) / ((p - 1) * (p - 2)) for p in P])
    SQ = mp.fsum([log(mpf(p)) / (p - 1) for p in Q])
    half = -SP + SQ
    return q, c0, hp, half, hp * (euler + half), mpf(1) / X


q, c0, hp, half, c2, tailerr = predicted(QSET)
print("Q (complement) =", QSET, "   q = least element of P =", q)
if q < 3:
    print("q = 2: boundary case, c_2 is not the right normalisation here.")
print("c_0 = prod_{p in Q}(1-1/p)        =", mp.nstr(c0, 18))
print("H_P(1,2)                          =", mp.nstr(hp, 18))
print("(1/2) d_s log H_P(1,2)            =", mp.nstr(half, 18))
print("gamma + that                      =", mp.nstr(euler + half, 18))
print("predicted c_2                     =", mp.nstr(c2, 18))
print("   (p-sum tail error bar ~", mp.nstr(tailerr, 3), ")")
print()
print("  k        f_k^P                 f_k - c_0           (f_k-c_0)*2^k      /c_2")
for k in KLIST:
    mp.dps = dps_for(k)
    _pz.clear()
    c0k = mp.fprod([1 - mpf(1) / p for p in QSET])
    v = fk(k, QSET)
    d = v - c0k
    r = d * mpf(2) ** k
    print("%3d  %s  %s  %s  %s" % (
        k, mp.nstr(v, 18), mp.nstr(d, 12), mp.nstr(r, 14),
        mp.nstr(r / c2, 10)))
    sys.stdout.flush()
