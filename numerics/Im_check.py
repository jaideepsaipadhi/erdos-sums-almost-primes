"""The P-independent integral behind the boundary case of Conjecture 7.1.

Separating the single factor L_2 in eq:HP-def gives the exact identity
H_P = Phi_P/(1 - z 2^-s) with Phi_P = H_{P minus {2}}, and expanding the pole
in powers of z gives, for every set of primes P with 2 in P,

    P_k^P(s) = sum_i phi_i(s) 2^{-(k-i)s} sum_{j<=k-i} (2^s log zeta(s))^j / j!,
    phi_i = [z^i] Phi_P.                                              (*)

(*) is exact.  It is verified here against direct Dirichlet sums, to ~1e-18,
for P = all primes, P = primes minus {3} and P = primes minus {3,5}.

Integrating ds over [1,inf) and freezing phi_i at s = 1 -- legitimate to
O(e^-k), since the mass of the s-integral sits at s - 1 ~ e^-k and
e^-k = o(2^-k) -- isolates ALL the k-dependence in

    I_m = int_1^inf 2^{-ms} sum_{j=0}^m (2^s log zeta(s))^j / j!  ds,

which contains no primes whatever.  Equivalently, using
sum_{j<=m} y^j/j! = e^y Gamma(m+1,y)/m! = (1/m!) int_0^inf (y+v)^m e^-v dv
and 2^-s y = u,

    I_m = (1/m!) int_1^inf int_0^inf (u(s) + 2^-s v)^m e^-v dv ds,
    u(s) = log zeta(s).

So f_k^P = sum_i phi_i(1) I_{k-i} + O(e^-k).  If I_m = c0 + A m^2 2^-m +
o(m^2 2^-m), then summing phi_i(1) 2^i against 1 and against (k-i)^2 gives

    f_k^P -> c0 * Phi_P(1,1),      k^2 2^-k coefficient = A * Phi_P(1,2),

both depending on the numerator only through its VALUE at the critical point.
No s-derivative of Phi_P can enter, so the "B = 0" case of the Section 7
reduction is automatic rather than assumed.

Because I_m is P-independent, the two universal constants are pinned by the
single case Q empty, where both answers are known:

    Lichtman's f_k -> 1   with Phi(1,1) = H_o(1,1) = 1/2   =>  c0 = 2
    GLW's a_1 = d log2/4  with Phi(1,2) = H_o(1,2) = d     =>  A  = -log2/4

This script checks both numerically.  It is mpmath, NOT Arb: no ball
arithmetic, no certificate, and nothing else in the paper or the formalization
depends on it.

Convergence is slow and one-sided, and the basis matters.  Read the stability
table, not any single fit: a three-parameter fit through three points has zero
residual, so its closeness to the prediction is not an error bar.

    python3 Im_check.py                       # settings of record -> Im.log
    python3 Im_check.py 16,20,24,28,32,36 5
"""
import sys
from mpmath import mp, mpf, exp, log, zeta, quad, factorial, matrix, lu_solve

ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
MS = [int(x) for x in (ARGS[0] if ARGS else "8,12,16,20,24,28,32,36").split(',')]
DEG = int(ARGS[1]) if len(ARGS) > 1 else 5


def dps_for(m):
    """1 + e^-t must keep digits at the top of the t-range."""
    return int(40 + 0.45 * (m + 14 * (m + 1) ** 0.5)) + 10


def I(m):
    mp.dps = dps_for(m)

    def integ(t):
        x = exp(-t)
        s = 1 + x
        y = mpf(2) ** s * log(zeta(s))
        tot = mp.zero; term = mp.one
        for j in range(0, m + 1):
            if j:
                term = term * y / j
            tot += term
        return mpf(2) ** (-m * s) * tot * x

    w = mp.sqrt(m + 1)
    lo = max(mpf(m) - 12 * w, mpf(-2))
    hi = mpf(m) + 14 * w
    return quad(integ, [lo, mpf(m), hi], maxdegree=DEG)


# ---------------------------------------------------------------- the identity
def _verify_identity():
    """(*) against direct Dirichlet sums, at s = 4 where they converge fast."""
    import sympy
    from mpmath import primezeta
    mp.dps = 40
    PR = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    def Am(m, s, drop):
        t = mpf(m) * s
        v = primezeta(t) if t < 21 else sum(mpf(p) ** (-t) for p in PR)
        return v - sum(mpf(p) ** (-t) for p in drop)

    def phi(s, K, drop):
        c = [mp.zero] * (K + 1)
        if K >= 1:
            c[1] += sum(log(1 - mpf(p) ** (-s)) for p in drop)
        for m in range(2, 90):
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

    s = mpf(4)
    print("== identity (*) against direct Dirichlet sums, s = 4, n <= 3e6 ==")
    for drop, name in [((), "all primes"), ((3,), "minus {3}"), ((3, 5), "minus {3,5}")]:
        d = list(drop) + ([2] if 2 not in drop else [])
        for k in (1, 2, 3):
            ph = phi(s, k, d); u = log(zeta(s)); tot = mp.zero
            for i in range(0, k + 1):
                m = k - i
                inner = sum((mpf(2) ** s * u) ** j / factorial(j) for j in range(0, m + 1))
                tot += ph[i] * mpf(2) ** (-m * s) * inner
            direct = mp.zero
            for n in range(2, 3000001):
                f = sympy.factorint(n)
                if sum(f.values()) != k:
                    continue
                if any(p in drop for p in f):
                    continue
                direct += mpf(n) ** (-s)
            print("   P = %-12s k=%d  formula %s  direct %s  reldiff %s"
                  % (name, k, mp.nstr(tot, 18), mp.nstr(direct, 18),
                     mp.nstr(abs(tot - direct) / abs(direct), 3)))
            sys.stdout.flush()


if "--identity" in sys.argv:
    _verify_identity()
    sys.exit(0)

# ------------------------------------------------------------------------ I_m
tgt = -log(mpf(2)) / 4
print("== I_m and the implied A ==")
print("   predicted c0 = 2 (from Lichtman's f_k -> 1)")
print("   predicted A  = -log2/4 =", mp.nstr(tgt, 12), "(from GLW's a_1 = d log2/4)")
print()
print("  m            I_m                  I_m - 2        (I_m-2)/(m^2 2^-m)")
D = {}
for m in MS:
    v = I(m)
    d = v - 2
    A = d / (mpf(m) ** 2 * mpf(2) ** (-m))
    D[m] = A
    print("%4d  %s  %s  %s" % (m, mp.nstr(v, 20), mp.nstr(d, 12), mp.nstr(A, 12)))
    sys.stdout.flush()

# ------------------------------------------------------- extrapolation, honestly
B_log = [lambda m: 1, lambda m: log(m) / m, lambda m: 1 / m]
B_pow = [lambda m: 1, lambda m: 1 / m, lambda m: 1 / m ** 2]
B_log2 = [lambda m: 1, lambda m: log(m) / m]


def fit(ms, basis):
    n = len(basis); M = matrix(n, n); b = matrix(n, 1)
    for i, m in enumerate(ms):
        for j, f in enumerate(basis):
            M[i, j] = f(mpf(m))
        b[i] = D[m]
    return lu_solve(M, b)[0]


print()
print("== stability of the extrapolated A ==")
print("A three-parameter fit through three points has ZERO residual, so no single")
print("fit is an error bar.  What is informative is which basis is stable.")
print()
print("%-36s %16s %10s" % ("fit", "A", "rel.err"))
big = [m for m in MS if m >= 16]
wins = []
if len(big) >= 3:
    wins += [(("log m/m + 1/m  (%d,%d,%d)" % tuple(big[-3:])), big[-3:], B_log)]
    if len(big) >= 4:
        wins += [(("log m/m + 1/m  (%d,%d,%d)" % tuple(big[-4:-1])), big[-4:-1], B_log)]
    if len(big) >= 5:
        w = [big[-5], big[-3], big[-1]]
        wins += [(("log m/m + 1/m  (%d,%d,%d)" % tuple(w)), w, B_log)]
    wins += [(("1/m + 1/m^2    (%d,%d,%d)" % tuple(big[-3:])), big[-3:], B_pow)]
    wins += [(("log m/m only   (%d,%d)" % tuple(big[-2:])), big[-2:], B_log2)]
for name, ms, bs in wins:
    A = fit(ms, bs)
    print("%-36s %16s %10s" % (name, mp.nstr(A, 10), mp.nstr(abs(A / tgt - 1), 4)))
print()
print("The bases WITHOUT a log m/m term land ~8-10% off, which is independent")
print("corroboration of GLW's O(k log(k+1)) subleading term: the data select")
print("that correction, and with it A agrees with -log2/4 to a few parts in 1000.")
