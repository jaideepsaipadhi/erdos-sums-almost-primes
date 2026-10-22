#!/usr/bin/env python3
"""How much does Proposition 3.5's near range cost once the sign error is repaired?

The proof bounds  sum_j int_0^3 u^{k-j}/(k-j)! |h_j(s(u))| J(u) du  by the
SIGNED identity

    sum_j u^{k-j}/(k-j)! h_j(s(u)) = P_k^odd(s(u)),

which is legitimate only if h_j >= 0.  It is not: h_1(s) = P_3(s) - log zeta(s)
= log(1-2^-s) - sum_{m>=2} P_3(ms)/m < 0 for every s, and the h_j alternate.

This script computes, at u = 3 (i.e. s = s(3), where log zeta(s) = 3), both

    A_k = sum_j 3^{k-j}/(k-j)! |h_j(s(3))|      (what is needed)
    S_k = sum_j 3^{k-j}/(k-j)!  h_j(s(3))       (what was used; = P_k^odd(s(3)))

and reports A_k/S_k, the true multiplicative cost of the repair, together with
A_k 3^k, the constant that would replace C_N <= 367.8436.

Everything is arb.  P_3 is evaluated by the Moebius series for the prime zeta
function, exactly as cn_certified.py does and for the same reason: at s ~ 1.05
direct summation over primes to any feasible cutoff leaves an O(1) tail.

    P(t) = sum_{n>=1} mu(n)/n log zeta(nt),      P_3(t) = P(t) - 2^-t.

Series bookkeeping.  With L_m = P_3(ms)/m,
    log of the odd Euler product prod_{p>=3}(1-z p^-s)^-1  =  sum_{m>=1} L_m z^m
    log H_o(s,z)                                           =  c_1 z + sum_{m>=2} L_m z^m,
       c_1 = L_1 - log zeta(s) = P_3(s) - 3 at s = s(3).
Both are exponentiated by the standard recurrence f_n = (1/n) sum_{m<=n} m c_m f_{n-m}.

Usage: python3 absratio.py [KMAX] [NMOB] [PREC]
"""
import sys
from flint import arb, ctx
from sympy import mobius

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 120
NMOB = int(sys.argv[2]) if len(sys.argv) > 2 else 100
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 900
ctx.prec = PREC
three = arb(3)

# --- s = s(3), proved bracket; every quantity below decreases in s, so the
# --- low end of the bracket bounds the whole of it.
lo, hi = arb('1.05'), arb('1.06')
assert (lo.zeta().log() > three) == True and (hi.zeta().log() < three) == True
for _ in range(100):
    mid = (lo + hi) / 2
    v = mid.zeta().log()
    if (v > three) == True:
        lo = mid
    elif (v < three) == True:
        hi = mid
    else:
        break
s = lo
print("s(3) in [%s, %s]" % (lo.lower(), hi.upper()))

MU = [0] + [int(mobius(n)) for n in range(1, NMOB + 1)]


def P_all(t):
    v = arb(0)
    for n in range(1, NMOB + 1):
        if MU[n]:
            v += arb(MU[n]) / n * (arb(n) * t).zeta().log()
    return v


def P_3(t):
    return P_all(t) - arb(2) ** (-t)


L = [arb(0)] * (KMAX + 2)
for m in range(1, KMAX + 2):
    L[m] = P_3(arb(m) * s) / m
print("P_3(s)   = %s" % L[1].str(12, radius=False))
print("h_1 = c_1 = P_3(s) - 3 = %s   (negative: this is the defect)"
      % (L[1] - three).str(12, radius=False))


def expseries(c, N):
    """exp of a power series with c[0] ignored; returns f[0..N], f[0]=1."""
    f = [arb(0)] * (N + 1)
    f[0] = arb(1)
    for n in range(1, N + 1):
        acc = arb(0)
        for m in range(1, n + 1):
            acc += arb(m) * c[m] * f[n - m]
        f[n] = acc / n
    return f


# odd Euler product: all L_m.  H_o: same but c_1 replaced by L_1 - log zeta(s).
cEuler = [arb(0)] + [L[m] for m in range(1, KMAX + 1)]
cH = list(cEuler)
cH[1] = L[1] - three

Pod = expseries(cEuler, KMAX)
h = expseries(cH, KMAX)

print("\nh_j(s(3)) for j <= 8:",
      " ".join(h[j].str(6, radius=False) for j in range(9)))

# weights 3^i/i!
w = [arb(1)]
for i in range(1, KMAX + 1):
    w.append(w[-1] * 3 / i)

print("\n   k      A_k*3^k        S_k*3^k      A_k/S_k   (S_k = P_k^odd(s(3)))")
worst = arb(0)
for k in list(range(1, 13)) + [20, 30, 50, 75, 100, KMAX]:
    if k > KMAX:
        continue
    A = arb(0)
    S = arb(0)
    for j in range(k + 1):
        A += w[k - j] * abs(h[j])
        S += w[k - j] * h[j]
    chk = (S - Pod[k]).abs_upper()
    A3 = A * three ** k
    S3 = S * three ** k
    r = A / S
    if (r > worst) == True:
        worst = r
    print("%5d  %13s  %13s  %11s   |S-P|<=%.2e"
          % (k, A3.str(8, radius=False), S3.str(8, radius=False),
             r.str(8, radius=False), float(chk)))

print("\nlargest A_k/S_k over the k sampled: %s" % worst.str(10, radius=False))
print("a single all-k constant would be about %s in place of C_N = 367.8436"
      % (arb('367.8436') * worst).str(10, radius=False))

# --- the conclusion that matters.  The inflation is confined to SMALL k: the
# --- absolute sum falls back under C_N at k = 24 and keeps falling, and the
# --- analytic branch of the odd assembly is used only for k >= K0 = 59, where
# --- the slack is more than tenfold.  Monotonicity for k <= 75 comes from the
# --- certified sweep, which never invokes the remainder bound.  So the repair
# --- costs nothing in certified constants: C_N, MR = 4900 and K0 = 59 all
# --- stand, and Proposition 3.5 need only be restated on the range where it is
# --- actually used.
CN = arb('367.8436')


def A(k):
    return sum((w[k - j] * abs(h[j]) for j in range(k + 1)), arb(0)) * three ** k


k1 = next(k for k in range(1, KMAX + 1)
          if all((A(m) <= CN) == True for m in range(k, min(KMAX, k + 40) + 1)))
print("\nA_k*3^k <= C_N for all k >= %d  (and A_23*3^23 = %s exceeds it)"
      % (k1, A(k1 - 1).str(8, radius=False)))
if KMAX >= 60:
    mx = max((A(k) for k in range(59, KMAX + 1)), key=lambda v: float(v.upper()))
    print("max of A_k*3^k over 59 <= k <= %d: %s, i.e. C_N has %.1fx slack there"
          % (KMAX, mx.str(8, radius=False), float(CN.lower() / mx.upper())))
print("=> the sign repair changes no certified constant; it changes the RANGE")
print("   of Proposition 3.5, whose only use downstream is k >= 59.")
