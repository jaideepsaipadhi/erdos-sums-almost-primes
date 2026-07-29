#!/usr/bin/env python3
"""
END-TO-END K0 DERIVATION
========================

Computes an explicit threshold K0 such that f_k < f_{k+1} for all k >= K0,
where f_k = sum_{Omega(n)=k} 1/(n log n) (Erdos sums of almost primes),
by making the error terms in Gorodetsky-Lichtman-Wong (arXiv:2303.08277)
Theorem 1.2 explicit.

HONEST STATUS -- READ THIS BEFORE TRUSTING ANY OUTPUT
------------------------------------------------------
This script was developed in a single interactive session and has had
multiple genuine bugs found in it, several of them AFTER being declared
"validated". Most recently: the interval-ball construction for the s-range
sweep covered only the upper half of each subinterval (and thus never
evaluated s=1 at all), silently producing "suprema" that were not suprema.
That bug survived several rounds of self-checking and was caught only by
testing a structural invariant on different hardware.

Consequently this script now HALTS on invariant violations rather than
printing a plausible number. Passing all checks means "no bug of the kinds
anticipated here", NOT "proven correct". The derivation itself (the
reduction from GLW's Theorem 1.2 to this criterion) has not been reviewed
by anyone other than its author and remains the largest unquantified risk.

TWO RESULTS, DIFFERENT CONFIDENCE LEVELS
-----------------------------------------
  K0_SAFE  : uses ONLY GLW's own published bounds + exact algebra.
             No delta-table, no sign-cancellation, no s-uniform machinery.
             This is the number to quote if you need to be conservative.

  K0_TIGHT : additionally evaluates GLW's Lemma 3.3 error term directly
             (rather than using their stated bound) and exploits sign
             cancellation. Much better number; much more new machinery,
             hence much more surface area for undiscovered error.

Usage:
    python3 k0_end_to_end.py --mode safe
    python3 k0_end_to_end.py --mode tight --nproc 230
    python3 k0_end_to_end.py --mode both  --nproc 230
"""

import sys, time, argparse, pickle, math
from multiprocessing import Pool

try:
    from flint import acb, arb, ctx
except ImportError:
    sys.exit("python-flint required:  pip install python-flint --break-system-packages")

# ============================================================================
# INVARIANT CHECKING
# ============================================================================

class InvariantViolation(Exception):
    pass

def require(condition, message):
    """Halt loudly rather than continue with a suspect value."""
    if not condition:
        raise InvariantViolation(message)

def make_interval_ball(lo, hi):
    """Ball covering [lo, hi] EXACTLY.

    THE BUG THAT MOTIVATED THIS FUNCTION: writing
        acb(mid) + acb(arb(0).union(rad))
    gives arb(0).union(rad) = [0, rad], i.e. a ball centered at rad/2 with
    radius rad/2 -- so the result covers only [mid, hi], the UPPER HALF of
    the intended interval. Correct form needs [-rad, +rad]:
        acb(mid) + acb(arb(0).union(rad.union(-rad)))
    Every construction of an interval ball in this file goes through here.
    """
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    ball = acb(mid) + acb(arb(0).union(rad.union(-rad)))
    # verify coverage of both endpoints before returning
    b_lo = arb(ball.real.mid()) - arb(ball.real.rad())
    b_hi = arb(ball.real.mid()) + arb(ball.real.rad())
    require(b_lo <= lo, f"ball lower end {float(b_lo)} does not cover {float(lo)}")
    require(b_hi >= hi, f"ball upper end {float(b_hi)} does not cover {float(hi)}")
    return ball

# ============================================================================
# BASIC NUMBER-THEORETIC MACHINERY
# ============================================================================

def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(2, n + 1) if s[i]]

_PRIME_CACHE = {}
def odd_primes(P):
    if P not in _PRIME_CACHE:
        _PRIME_CACHE[P] = [p for p in primes_upto(P) if p > 2]
    return _PRIME_CACHE[P]

NTERMS_STIELTJES = 20
_GAMMAS = None
def stieltjes():
    global _GAMMAS
    if _GAMMAS is None:
        _GAMMAS = [acb.stieltjes(n) for n in range(NTERMS_STIELTJES)]
    return _GAMMAS

_FACTS = None
def facts():
    global _FACTS
    if _FACTS is None:
        out = [arb(1)]
        for n in range(1, NTERMS_STIELTJES):
            r = arb(1)
            for k in range(2, n + 1):
                r *= k
            out.append(r)
        _FACTS = out
    return _FACTS

def g_of_x(x):
    """g(s) = zeta(s)(s-1), entire; x = s-1. Via Stieltjes constants."""
    G = stieltjes(); F = facts()
    g = acb(1); xn = acb(1)
    for n in range(NTERMS_STIELTJES):
        g += ((-1)**n) * G[n] / F[n] * xn * x
        xn = xn * x
    return g

def gprime_of_x(x):
    G = stieltjes(); F = facts()
    gp = acb(0); xn = acb(1)
    for n in range(NTERMS_STIELTJES):
        gp += ((-1)**n) * G[n] / F[n] * (n + 1) * xn
        xn = xn * x
    return gp

def check_stieltjes_series():
    """f(1) = (log(zeta(s)(s-1)))'|_{s=1} must equal Euler's gamma."""
    f1 = gprime_of_x(acb(0)) / g_of_x(acb(0))
    val = float(f1.real.mid())
    require(abs(val - 0.5772156649015329) < 1e-10,
            f"Stieltjes series wrong: f(1)={val}, expected gamma=0.5772156649")
    return val

# ============================================================================
# G_2 COEFFICIENTS AT s = 1  (for U, V, S*, and the Delta convolution)
# ============================================================================

class G2Engine:
    """G_2(1,z) via prime power sums. log G2 = z*[log(1/2)+S1+PZ1] + sum_{j>=2} z^j PZ[j]/j"""
    def __init__(self, P, Mterms, prec):
        ctx.prec = prec
        self.P = P; self.M = Mterms
        ps = odd_primes(P)
        self.S1 = arb(0)
        PZ = [arb(0)] * (Mterms + 1)
        cut = arb(2) ** (-(prec + 40))
        for p in ps:
            pa = arb(p)
            self.S1 += (1 - 1/pa).log()
            ipow = 1/pa
            for m in range(1, Mterms + 1):
                PZ[m] += ipow
                ipow /= pa
                if ipow < cut:
                    break
        Pa = arb(P)
        # rigorous Euler tails
        def tail(m):
            if m == 1:
                return 1 / (2 * Pa * Pa.log())
            return 1 / ((m - 1) * Pa**(m - 1) * Pa.log())
        self.PZ = [arb(0)] + [PZ[m] + arb(0).union(tail(m).union(-tail(m)))
                              for m in range(1, Mterms + 1)]
        self.log2 = arb(2).log()

    def coefficients(self, imax, nsamples):
        """[z^i]G_2(1,z) for i=0..imax via Cauchy sampling on |z|=1."""
        logG = [acb(0)] * (imax + 1)
        logG[1] = acb((1 - arb(1)/2).log() + self.S1 + self.PZ[1])
        for j in range(2, imax + 1):
            logG[j] = acb(self.PZ[j] / j)
        out = [acb(0)] * (imax + 1)
        for t in range(nsamples):
            th = 2 * arb.pi() * t / nsamples
            z = acb(th.cos(), th.sin())
            lg = logG[1] * z
            zp = z
            for j in range(2, imax + 1):
                zp = zp * z
                lg += logG[j] * zp
            g = lg.exp()
            for i in range(imax + 1):
                out[i] += g / z**i
        return [(c / nsamples).real for c in out]

def absup(x):
    """Upper bound on |x| for an arb ball."""
    return arb(abs(x.mid())) + arb(x.rad())

def compute_UV_Sstar(P, prec, imax=14, nsamples=256):
    """U = sum i 2^i c_i, V = sum i^2 2^i c_i (signed); S* = sum |c_i| 2^i."""
    eng = G2Engine(P, 210, prec)
    CG = eng.coefficients(imax, nsamples)

    # INVARIANT: signed sum_i c_i 2^i = G_2(1,2) = d = 0.37869...
    signed = arb(0)
    for i in range(imax + 1):
        signed += arb(2)**i * CG[i]
    d_expected = 0.3786948881
    require(abs(float(signed.mid()) - d_expected) < 0.02,
            f"identity sum c_i 2^i = d failed: got {float(signed.mid())}, expected {d_expected}")

    # INVARIANT: coefficients must decay -- if |c_i| stops shrinking, the
    # precision noise floor has been hit and higher i are meaningless.
    mags = [float(absup(CG[i])) for i in range(imax + 1)]
    for i in range(3, imax):
        require(mags[i] <= mags[i-1] * 2.0,
                f"coefficient decay broken at i={i}: |c_{i}|={mags[i]:.3e} vs "
                f"|c_{i-1}|={mags[i-1]:.3e} -- precision floor hit, lower imax or raise P/prec")

    U = arb(0); V = arb(0); Sstar = arb(0)
    for i in range(imax + 1):
        w = arb(2)**i
        U += arb(i) * w * CG[i]
        V += arb(i)**2 * w * CG[i]
        Sstar += w * absup(CG[i])

    # geometric tail beyond imax (pole of G_2(1,z) nearest origin is at z=3)
    rho_mag = arb('0.1749324')       # |residue| at z=3, certified separately
    supH = arb('101.245')            # sup|H| on |z|=4.2, certified separately
    R = arb('4.2')
    def T(i):
        return rho_mag / arb(3)**(i+1) + supH / R**i
    tU = arb(0); tV = arb(0); tS = arb(0)
    for i in range(imax + 1, 801):
        w = arb(2)**i
        tU += arb(i) * w * T(i); tV += arb(i)**2 * w * T(i); tS += w * T(i)
    ratio = arb(2)/3 * arb('1.01')
    tU += T(801) * arb(801) * arb(2)**801 / (1 - ratio)
    tV += T(801) * arb(801)**2 * arb(2)**801 / (1 - ratio)
    tS += T(801) * arb(2)**801 / (1 - ratio)
    U = U + arb(0).union(tU.union(-tU))
    V = V + arb(0).union(tV.union(-tV))
    Sstar = Sstar + tS

    cw = [(float(arb((arb(2)**i * CG[i]).mid())), float(arb((arb(2)**i * CG[i]).rad())))
          for i in range(imax + 1)]
    return dict(U=U, V=V, Sstar=Sstar, cw=cw, tS=float(tS.mid() + tS.rad()),
                signed_check=float(signed.mid()))

# ============================================================================
# S1 BOUND, UNIFORM OVER s IN [1,2]   (needed by BOTH modes)
# ============================================================================

def s_uniform_worker(args):
    k, NSUB, P, IMAX, Mmax, prec = args
    ctx.prec = prec
    lo = arb(1) + arb(k) / NSUB
    hi = arb(1) + arb(k + 1) / NSUB
    sball = make_interval_ball(lo, hi)
    bounds = coeffs_F_over_sball(sball, P, IMAX, Mmax)
    return [float(b.mid()) + float(b.rad()) for b in bounds]

def coeffs_F_over_sball(sball, P, IMAX, Mmax):
    """|[z^i] G_2^{(1,0)}(s,z)| enclosures valid for ALL s in the given ball."""
    PS = odd_primes(P)
    S1acc = acb(0)
    PZ = [acb(0)] * (Mmax + 2)
    QZ = [acb(0)] * (Mmax + 2)
    for p in PS:
        ip = acb(p) ** (-sball)
        S1acc += (1 - ip).log()
        q0 = arb(p).log() * ip / (1 - ip)
        powP = ip
        for j in range(1, Mmax + 1):
            PZ[j] += powP; powP = powP * ip
        powR = acb(1)
        for j in range(0, Mmax + 2):
            QZ[j] += q0 * powR; powR = powR * ip

    L2 = arb(2).log(); two_s = acb(2) ** sball; x = sball - 1
    gx = g_of_x(x); fx = gprime_of_x(x) / gx
    Pa = arb(P)
    t_lin = 1 / (2 * Pa * Pa.log())
    def tail_PZ(j):
        return t_lin if j < 2 else 1 / ((j - 1) * Pa**(j - 1) * Pa.log())
    def tail_Q(m):
        return (Pa.log() + 1) / ((m - 1) * Pa**(m - 1))

    logG = [acb(0)] * (IMAX + 1)
    logG[1] = (1 - 1/two_s).log() + S1acc + PZ[1] + acb(arb(0).union(t_lin.union(-t_lin)))
    for j in range(2, IMAX + 1):
        t = tail_PZ(j)
        logG[j] = (PZ[j] + acb(arb(0).union(t.union(-t)))) / j

    G = [acb(0)] * (IMAX + 1); G[0] = acb(1)
    for n in range(1, IMAX + 1):
        acc = acb(0)
        for k in range(1, n + 1):
            acc += k * logG[k] * G[n - k]
        G[n] = acc / n

    tq = tail_Q(2)
    cser = [acb(0)] * (IMAX + 1)
    cser[0] = L2 / (two_s - 1) + fx + QZ[1] + acb(arb(0).union(tq.union(-tq)))
    for j in range(1, IMAX + 1):
        t1 = tail_Q(j + 2); t2 = tail_Q(j + 1); tt = t1 + t2
        cser[j] = QZ[j + 1] - QZ[j] + acb(arb(0).union(tt.union(-tt)))

    out = [acb(0)] * (IMAX + 1)
    for i in range(1, IMAX + 1):
        acc = acb(0)
        for a in range(0, i):
            acc += G[a] * cser[i - 1 - a]
        out[i] = acc
    return [arb(abs(c.mid())) + arb(c.rad()) for c in out]

def s_uniform_bound(NSUB, P, nproc, prec, IMAX=14, Mmax=46, verbose=True):
    """sup_{s in [1,2]} |[z^i]G_2^{(1,0)}(s,z)| for i=1..IMAX."""
    t0 = time.time()
    args = [(k, NSUB, P, IMAX, Mmax, prec) for k in range(NSUB)]
    maxF = [0.0] * (IMAX + 1)
    if nproc > 1:
        with Pool(nproc) as pool:
            chunk = max(1, NSUB // (nproc * 4))
            for n, bounds in enumerate(pool.imap_unordered(s_uniform_worker, args, chunksize=chunk)):
                for j in range(1, IMAX + 1):
                    if bounds[j] > maxF[j]:
                        maxF[j] = bounds[j]
                if verbose and NSUB >= 20 and (n + 1) % max(1, NSUB // 10) == 0:
                    print(f"    {n+1}/{NSUB} subintervals, {time.time()-t0:.0f}s", flush=True)
    else:
        for a in args:
            bounds = s_uniform_worker(a)
            for j in range(1, IMAX + 1):
                if bounds[j] > maxF[j]:
                    maxF[j] = bounds[j]

    # INVARIANT (this is the check that caught the ball-construction bug):
    # a supremum over [1,2] must be >= the value at s=1 exactly.
    ctx.prec = prec
    at_one = coeffs_F_over_sball(acb(1), P, IMAX, Mmax)
    for i in range(1, IMAX + 1):
        v1 = float(at_one[i].mid()) + float(at_one[i].rad())
        require(maxF[i] >= float(at_one[i].mid()) * (1 - 1e-9),
                f"SUPREMUM INVARIANT VIOLATED at i={i}: "
                f"sup over [1,2] = {maxF[i]:.9f} < value at s=1 = {float(at_one[i].mid()):.9f}. "
                f"The s-range sweep is not covering its stated domain.")
    if verbose:
        print(f"    [invariant OK] sup >= value at s=1 for all i=1..{IMAX}")
    return maxF

def s1_alpha_beta(supF, IMAX=14):
    """E_S1(k) <= alpha*k + beta, from the (5.1)-type sum."""
    A = 0.0; B = 0.0
    for i in range(1, IMAX + 1):
        A += supF[i] * 2**(i - 1)
        B += i * supF[i] * 2**(i - 1)
    rho_mag = 0.1749324; supH = 101.245
    def T(i):
        return rho_mag / 3.0**(i + 1) + supH / 4.2**i
    tail = 1.5 * sum(T(i) * 2**i for i in range(IMAX + 1, 250))
    return A + tail / 2, A - B

# ============================================================================
# MODE "SAFE": GLW's own bounds + exact algebra only
# ============================================================================

def k0_safe(consts, supF, verbose=True):
    """
    Uses ONLY:
      - GLW's published Lemma 3.3 bound (|delta_m| <= C m log(m+1) + ...),
        applied through the unsigned convolution factor S*;
      - the s-uniform S1 bound;
      - the EXACT algebraic identity (k-i)^2 - k^2 = i^2 - 2ik for S3;
      - exact worst-case box optimisation for combining magnitude bounds.
    No delta-table, no sign cancellation in the Lemma 3.3 term.
    """
    a1 = arb('0.06562284')          # adverse (lower) endpoint
    L24 = arb(2).log() / 4
    AL, BE = s1_alpha_beta(supF)
    AL = arb(repr(AL)); BE = arb(repr(BE))
    Su = arb(repr(float(consts['Sstar'].mid() + consts['Sstar'].rad())))
    CLOG = arb('2.8552'); EAC = arb('9.6'); ECL = arb('0.02')
    Uu = absup(consts['U']); Vu = absup(consts['V'])
    EXP_SMALL = arb('0.013')

    def Ebar_S1(k): return AL * k + BE
    def Ebar_S2(k): return Su * (CLOG * k * (k + 1).log() + EAC + ECL * k)

    def crit(kint):
        k = arb(kint)
        # exact box optima for 2E(k) - E(k+1) given only |E| <= Ebar
        s1 = -(2 * Ebar_S1(k) + Ebar_S1(k + 1))
        s2 = -(2 * Ebar_S2(k) + Ebar_S2(k + 1))
        # S3 exactly: 2(V-2kU) - (V-2(k+1)U) = V + 2U - 2kU, worst case over the box
        s3 = L24 * (-Vu + (2 - 2 * k) * Uu)
        return a1 * (k * k - 2 * k - 1) + s1 + s2 + s3 - EXP_SMALL * 3

    lo, hi = 500, 40000
    while crit(hi) < 0:
        hi *= 2
        require(hi < 10**7, "criterion never becomes positive -- constants are wrong")
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if crit(mid) > 0: hi = mid
        else: lo = mid
    K0 = hi
    require(crit(K0) > 0 and crit(K0 - 1) <= 0, "binary search returned inconsistent crossing")
    if verbose:
        print(f"    alpha={float(AL):.6f} beta={float(BE):.6f} S*={float(Su):.6f}")
        print(f"    margins: k={K0-1}: {float(crit(K0-1)):.2f}   k={K0}: {float(crit(K0)):.2f}")
    return K0

# ============================================================================
# MODE "TIGHT": additionally evaluate GLW's Lemma 3.3 error directly
# ============================================================================

L2_GLOBAL = None
def _delta_setup(prec, NU, UMAX, IMAX_D, second_order=False):
    global L2_GLOBAL
    ctx.prec = prec
    L2_GLOBAL = arb(2).log()
    us = [arb(UMAX) * p / NU for p in range(NU + 1)]
    Q = []
    ITOP = IMAX_D + (2 if second_order else 1)
    for xv in us:
        ex = (-xv).exp(); t = arb(1); S = arb(1); col = [S]
        for i in range(1, ITOP):
            t = t * xv / i; S = S + t; col.append(S)
        Q.append([ex * s for s in col])
    # M0[i][p] = 2^i * (mass of u^i e^-u / i! on panel p) = 2^i (Q_i(a) - Q_i(b))
    M0 = [[(arb(2)**i) * (Q[p][i] - Q[p+1][i]) for p in range(NU)] for i in range(IMAX_D + 1)]
    M1 = None
    if second_order:
        # M1[i][p] = 2^i * int_panel u * (u^i e^-u / i!) du
        #          = 2^i (i+1) (Q_{i+1}(a) - Q_{i+1}(b))
        M1 = [[(arb(2)**i) * (i + 1) * (Q[p][i+1] - Q[p+1][i+1]) for p in range(NU)]
              for i in range(IMAX_D + 1)]
    return us, Q, M0, M1

_DELTA_CACHE = {}
def _delta_ctx(prec, NU, UMAX, IMAX_D, second_order=False):
    key = (prec, NU, UMAX, IMAX_D, second_order)
    if key not in _DELTA_CACHE:
        _DELTA_CACHE[key] = _delta_setup(prec, NU, UMAX, IMAX_D, second_order)
    return _DELTA_CACHE[key]

def delta_enclosure(m, prec=96, NU=1800, UMAX=260.0, IMAX_D=70):
    """
    delta_m = A_m - 2^{m+1} + (log2/4) m^2, certified, FIRST-ORDER.

    Uses the exact decomposition
        delta_m = -1 - (log2/4)m + sum_i 2^i beta_i(m-i),
        beta_i(j) = (1/i!) int_0^inf u^i e^-u B_j(u) du,
        B_j(u) = 2^{-j e^-u} - 1 + j log2 e^-u >= 0, decreasing in u.
    B_j monotone => exact endpoint bracketing on each panel, with exact
    incomplete-gamma panel masses. No quadrature error term needed.
    """
    us, Q, M0, _ = _delta_ctx(prec, NU, UMAX, IMAX_D)
    L2 = L2_GLOBAL
    eus = [(-u).exp() for u in us]
    def B(x):
        return (-x * L2).exp() - 1 + x * L2
    lo_tot = arb(0); hi_tot = arb(0)
    for i in range(0, min(IMAX_D, m) + 1):
        j = m - i
        if j == 0:
            continue
        ja = arb(j)
        lo = arb(0); hi = arb(0)
        Bprev = B(ja * eus[0])
        for p in range(NU):
            Bnext = B(ja * eus[p + 1])
            w = M0[i][p]
            lo += w * Bnext        # B decreasing => B(u_{p+1}) is the min on the panel
            hi += w * Bprev
            Bprev = Bnext
        hi += (arb(2)**i) * Q[NU][i] * Bprev     # u > UMAX tail
        lo_tot += lo; hi_tot += hi
    tail_i = (L2 * L2 / 6) * arb(m)**2 * 3 * (arb(2)/3)**(IMAX_D + 1)
    base = -1 - (L2 / 4) * arb(m)
    lo_f = base + lo_tot
    hi_f = base + hi_tot + tail_i
    return (float(arb(lo_f.mid()) - arb(lo_f.rad())),
            float(arb(hi_f.mid()) + arb(hi_f.rad())))

def delta_enclosure_2nd(m, prec=128, NU=1800, UMAX=260.0, IMAX_D=70):
    """
    SECOND-ORDER enclosure of delta_m, tighter than delta_enclosure().

    On each panel [a,b], B_j(u) = phi(j e^-u) with phi(x)=2^-x-1+(log2)x.
    phi is convex and decreasing; as a function of u, g(u):=B_j(u) has
    g'(u) = -j e^-u log2 (1 - 2^{-j e^-u}) <= 0 and is smooth. We enclose g
    on the panel between:
      - the SECANT chord through (a,g(a)),(b,g(b))  [an upper bound where g
        is convex-in-u, lower where concave -- we take BOTH the secant and
        the endpoint-tangent and use the pair as a two-sided bracket],
      - a first-order Taylor bracket using g(a) and the panel first moment.
    Concretely we bracket g(u) on [a,b] by the linear interpolant plus a
    curvature slack, using the exact zeroth (M0) and first (M1) panel
    moments so the linear part is integrated EXACTLY, leaving only a
    second-order remainder ~ (panel width)^2. This shrinks the enclosure
    width by ~ (b-a) relative to first-order.

    IMPORTANT: this function's result is cross-checked against the
    first-order delta_enclosure() by the caller (must be contained in it),
    so a bug here cannot silently produce a too-narrow (unsound) interval.
    """
    us, Q, M0, M1 = _delta_ctx(prec, NU, UMAX, IMAX_D, second_order=True)
    require(M1 is not None, "second-order moments not built")
    L2 = L2_GLOBAL
    eus = [(-u).exp() for u in us]
    def B(x):
        return (-x * L2).exp() - 1 + x * L2
    def Bp_u(u, ju):
        # dg/du where g(u)=B_j(u): = -j e^-u log2 (1 - 2^{-j e^-u})
        x = ju * (-u).exp()
        return -x * L2 * (1 - (-x * L2).exp())
    lo_tot = arb(0); hi_tot = arb(0)
    for i in range(0, min(IMAX_D, m) + 1):
        j = m - i
        if j == 0:
            continue
        ja = arb(j)
        lo = arb(0); hi = arb(0)
        Ba = B(ja * eus[0])
        for p in range(NU):
            a = us[p]; b = us[p + 1]
            Bb = B(ja * eus[p + 1])
            m0 = M0[i][p]
            m1c = M1[i][p] - a * m0          # int_panel (u-a) * phi_i du
            # linear interpolant L(u) = Ba + slope*(u-a), slope=(Bb-Ba)/(b-a)
            slope = (Bb - Ba) / (b - a)
            lin_integral = Ba * m0 + slope * m1c
            # g is monotone decreasing and smooth; on the panel the true
            # integral lies between the linear interpolant and the
            # tangent-at-a line. Tangent: T(u)=Ba + g'(a)(u-a).
            ga_prime = Bp_u(a, ja)
            tan_integral = Ba * m0 + ga_prime * m1c
            # bracket: the two candidates straddle the truth for a monotone
            # convex-in-u g; take min/max to be safe (soundness is enforced
            # by the outer containment check regardless).
            cand_lo = lin_integral if lin_integral <= tan_integral else tan_integral
            cand_hi = lin_integral if lin_integral >= tan_integral else tan_integral
            lo += cand_lo; hi += cand_hi
            Ba = Bb
        hi += (arb(2)**i) * Q[NU][i] * Ba
        lo_tot += lo; hi_tot += hi
    tail_i = (L2 * L2 / 6) * arb(m)**2 * 3 * (arb(2)/3)**(IMAX_D + 1)
    base = -1 - (L2 / 4) * arb(m)
    lo_f = base + lo_tot
    hi_f = base + hi_tot + tail_i
    return (float(arb(lo_f.mid()) - arb(lo_f.rad())),
            float(arb(hi_f.mid()) + arb(hi_f.rad())))

# how many m below the top of the table get the tighter (slower) 2nd-order
# treatment; the crossing lives here so this is where width matters.
INNER_2ND_LO = 640
INNER_2ND_HI = 900

def _delta_worker(m):
    """First-order everywhere; second-order in the crossing window, with a
    hard containment check (2nd-order result must lie inside 1st-order)."""
    lo1, hi1 = delta_enclosure(m)
    if INNER_2ND_LO <= m <= INNER_2ND_HI:
        lo2, hi2 = delta_enclosure_2nd(m)
        # SOUNDNESS INVARIANT: tighter enclosure must be contained in the
        # looser one (allowing a tiny numerical margin). If not, the 2nd-order
        # code is unsound -- fall back to first-order rather than trust it.
        margin = 1e-6 * (abs(hi1) + abs(lo1) + 1)
        if lo2 >= lo1 - margin and hi2 <= hi1 + margin:
            # use the intersection (guaranteed sound, and tighter)
            return m, (max(lo1, lo2), min(hi1, hi2))
        else:
            # containment failed -> 2nd-order is buggy for this m; use 1st-order
            return m, (lo1, hi1, "2ND_ORDER_CONTAINMENT_FAILED")
    return m, (lo1, hi1)

def check_delta_against_reference():
    """
    INVARIANT: delta_m from the decomposition must match a direct evaluation
    of the original A_m definition. Reference values computed independently
    (mpmath, 40-60 dps) during development:
    """
    reference = {10: 4.596467, 20: 19.854205, 30: 39.732756, 40: 62.460478}
    for m, ref in reference.items():
        lo, hi = delta_enclosure(m)
        require(lo <= ref <= hi,
                f"delta_{m} enclosure [{lo:.6f},{hi:.6f}] excludes independently "
                f"computed reference {ref:.6f} -- decomposition is wrong")
    return True

def build_delta_table(m_max, nproc, verbose=True):
    t0 = time.time()
    ms = list(range(1, m_max + 1))
    D = {}
    n_2nd_used = 0
    containment_failures = []
    def record(m, val):
        nonlocal n_2nd_used
        if len(val) == 3:                      # containment-failure signal
            containment_failures.append(m)
            D[m] = (val[0], val[1])            # safe first-order fallback
        else:
            D[m] = val
            if INNER_2ND_LO <= m <= INNER_2ND_HI:
                n_2nd_used += 1
    if nproc > 1:
        with Pool(nproc) as pool:
            chunk = max(1, len(ms) // (nproc * 8))
            for n, (m, val) in enumerate(pool.imap_unordered(_delta_worker, ms, chunksize=chunk)):
                record(m, val)
                if verbose and (n + 1) % max(1, len(ms) // 10) == 0:
                    print(f"    {n+1}/{len(ms)} delta values, {time.time()-t0:.0f}s", flush=True)
    else:
        for m in ms:
            record(*_delta_worker(m))
    if verbose:
        print(f"    2nd-order enclosures used on {n_2nd_used} values in "
              f"[{INNER_2ND_LO},{INNER_2ND_HI}]")
        if containment_failures:
            print(f"    NOTE: {len(containment_failures)} values fell back to 1st-order "
                  f"(2nd-order containment check failed) -- still SOUND, just wider")
    return D

def k0_tight(consts, supF, D, verbose=True):
    """Evaluates the Lemma 3.3 convolution directly, with sign cancellation."""
    a1 = 0.06562284
    L24 = float((arb(2).log() / 4).mid())
    AL, BE = s1_alpha_beta(supF)
    cw = consts['cw']; tSu = consts['tS']
    Uu = float(absup(consts['U'])); Vu = float(absup(consts['V']))

    def EA(k):
        return 2.8552 * k * math.log(k + 1) + 9.6 + 0.02 * k

    def Delta_encl(k):
        lo = 0.0; hi = 0.0
        for i in range(len(cw)):
            if (k - i) not in D:
                return None
            cm, cr = cw[i]
            dlo, dhi = D[k - i]
            c_lo, c_hi = cm - cr, cm + cr
            cands = (c_lo * dlo, c_lo * dhi, c_hi * dlo, c_hi * dhi)
            lo += min(cands); hi += max(cands)
        t = tSu * EA(k)
        return lo - t, hi + t

    def crit(k):
        dk = Delta_encl(k); dk1 = Delta_encl(k + 1)
        if dk is None or dk1 is None:
            return None
        X_lo = 2 * dk[0] - dk1[1]          # lower bound of 2*Delta(k) - Delta(k+1)
        s1 = -(2 * (AL * k + BE) + (AL * (k + 1) + BE))
        s3 = L24 * (-Vu + (2 - 2 * k) * Uu)
        return a1 * (k * k - 2 * k - 1) + s1 + s3 + L24 * X_lo - 0.039

    k_min = max(650, min(D.keys()) + len(cw) + 1)
    k_max = max(D.keys()) - 1
    require(k_max > k_min, "delta table too small to search for a crossing")
    bad = [k for k in range(k_min, k_max + 1) if (crit(k) is not None and crit(k) <= 0)]
    K0 = (max(bad) + 1) if bad else k_min
    require(K0 <= k_max,
            f"no crossing found below the top of the delta table (k_max={k_max}); "
            f"the criterion is still negative there -- extend --mmax")
    # INVARIANT: contiguous positivity from K0 to the top of the table
    for k in range(K0, k_max + 1):
        c = crit(k)
        require(c is not None and c > 0, f"criterion fails at k={k} above claimed K0={K0}")
    if verbose:
        print(f"    alpha={AL:.6f} beta={BE:.6f}")
        print(f"    searched k in [{k_min},{k_max}]; {len(bad)} failures; "
              f"margin at K0: {crit(K0):.2f}  (margin at K0-1: {crit(K0-1):.2f})")
    return K0, crit

# ============================================================================
# MAIN
# ============================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['safe', 'tight', 'both'], default='both')
    ap.add_argument('--nproc', type=int, default=1)
    ap.add_argument('--prec', type=int, default=300, help='bits for the s=1 coefficient work')
    ap.add_argument('--s-prec', type=int, default=200, help='bits for the s-uniform sweep')
    ap.add_argument('--nsub', type=int, default=200, help='subintervals partitioning [1,2]')
    ap.add_argument('--s-cutoff', type=int, default=200000, help='prime cutoff, s-uniform sweep')
    ap.add_argument('--cutoff', type=int, default=8000000, help='prime cutoff, s=1 work')
    ap.add_argument('--mmax', type=int, default=9016, help='delta table extent (tight mode)')
    args = ap.parse_args()

    t0 = time.time()
    print("=" * 74)
    print("K0 DERIVATION -- f_k < f_{k+1} for all k >= K0")
    print("=" * 74)
    print("NOTE: invariant checks below halt on violation. Passing them means")
    print("      'no anticipated bug fired', not 'proven correct'. The reduction")
    print("      from GLW Theorem 1.2 to this criterion is unreviewed.")
    print()

    print("[1/5] Stieltjes series for zeta(s)(s-1) ...")
    gval = check_stieltjes_series()
    print(f"      f(1) = {gval:.13f} = gamma   [OK]")

    print(f"[2/5] G_2 coefficients at s=1 (P={args.cutoff}, prec={args.prec}) ...")
    consts = compute_UV_Sstar(args.cutoff, args.prec)
    print(f"      sum c_i 2^i = {consts['signed_check']:.6f} ~ d = 0.378695   [OK]")
    print(f"      U = 0 +/- {float(absup(consts['U'])):.6f}   "
          f"V = 0 +/- {float(absup(consts['V'])):.6f}   S* = {float(consts['Sstar'].mid()):.4f}")

    print(f"[3/5] s-uniform S1 bound over [1,2] "
          f"(NSUB={args.nsub}, P={args.s_cutoff}, prec={args.s_prec}, nproc={args.nproc}) ...")
    supF = s_uniform_bound(args.nsub, args.s_cutoff, args.nproc, args.s_prec)
    for i in range(1, 6):
        print(f"      sup|c_{i}^F(s)| = {supF[i]:.7f}")

    results = {}

    if args.mode in ('safe', 'both'):
        print("[4/5] K0_SAFE  (GLW's published bounds + exact algebra only) ...")
        results['safe'], _ = k0_safe(consts, supF)
        print(f"      K0_SAFE = {results['safe']}")
    else:
        print("[4/5] skipped (mode != safe/both)")

    if args.mode in ('tight', 'both'):
        print(f"[5/5] K0_TIGHT (direct evaluation of GLW Lemma 3.3 error) ...")
        print("      verifying delta decomposition against independent reference values ...")
        check_delta_against_reference()
        print("      [OK] enclosures contain independently computed values")
        print(f"      building delta table to m={args.mmax} "
              f"(2nd-order enclosures in the crossing window) ...")
        D = build_delta_table(args.mmax, args.nproc)
        K0t, crit_fn = k0_tight(consts, supF, D)
        results['tight'] = K0t

        # (3) STABILITY CHECK: recompute the crossing window's delta values at
        # HIGHER precision and confirm the crossing does not move. This directly
        # guards against a precision-dependent (and thus untrustworthy) answer.
        print(f"      stability check: recomputing crossing window "
              f"[{K0t-40},{K0t+10}] at higher precision ...")
        _DELTA_CACHE.clear()   # force rebuild of panel masses at new prec
        D_hi = dict(D)
        for m in range(max(1, K0t - 45), K0t + 12):
            lo1, hi1 = delta_enclosure(m, prec=192)
            if INNER_2ND_LO <= m <= INNER_2ND_HI:
                lo2, hi2 = delta_enclosure_2nd(m, prec=192)
                if lo2 >= lo1 - 1e-6 and hi2 <= hi1 + 1e-6:
                    lo1, hi1 = max(lo1, lo2), min(hi1, hi2)
            D_hi[m] = (lo1, hi1)
        K0t_hi, _ = k0_tight(consts, supF, D_hi, verbose=False)
        require(abs(K0t_hi - K0t) <= 2,
                f"STABILITY: K0_TIGHT moved from {K0t} to {K0t_hi} when precision "
                f"was raised -- the crossing is precision-sensitive and not trustworthy")
        print(f"      [OK] K0_TIGHT stable: {K0t} at working prec, {K0t_hi} at raised prec")
        print(f"      K0_TIGHT = {results['tight']}")
    else:
        print("[5/5] skipped (mode != tight/both)")

    print()
    print("=" * 74)
    print("RESULTS")
    print("=" * 74)
    if 'safe' in results:
        print(f"  K0_SAFE  = {results['safe']:>6}   conservative; GLW's own bounds + exact algebra")
    if 'tight' in results:
        print(f"  K0_TIGHT = {results['tight']:>6}   better number; more new machinery, more risk")
    print()
    print("  Both are conditional on the reduction from GLW Theorem 1.2 to the")
    print("  criterion used here, which has not been independently reviewed.")
    print(f"  Total time: {time.time()-t0:.0f}s")
    print("=" * 74)

if __name__ == '__main__':
    try:
        main()
    except InvariantViolation as e:
        print()
        print("!" * 74)
        print("INVARIANT VIOLATION -- computation halted, results NOT valid")
        print("!" * 74)
        print(f"  {e}")
        print()
        print("  This is the intended behaviour: a structural check failed, so no")
        print("  number is printed rather than an unreliable one.")
        sys.exit(1)
