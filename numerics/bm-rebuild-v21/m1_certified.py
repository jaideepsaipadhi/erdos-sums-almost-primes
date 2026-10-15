#!/usr/bin/env python3
"""Certified M1_R2.9 and M2sup_R2.9:

    M1    = sup_{|z| = R, s in [1,2]} |d_s   G_2(s,z)|
    M2sup = sup_{|z| = R, s in [1,2]} |d_s^2 G_2(s,z)|      (R = 2.9)

These two constants are read by k1_far_range.py, crit_refined.py,
crossval_refined.py and crit_assembly.py, and they enter the trusted base as
the Cauchy tails

    |beta_i|  <= M1    R^-i,        |gammahat_i| <= M2sup R^-i,

(see verify.py's "Cauchy tail at 2.9" check and k1_far_range.py lines 56-61,
where alpha_+ = (sum_{i<=30} beta_i 2^i)/2 + M1 (2/R)^31/(1-2/R)/2).  Until
this script existed, nothing in the repository produced them: they were stored
in m1_constant.json and gamma_constant.json with no derivation on file.

This is the unrestricted analogue of odd-proof/numerics/mr_deriv_sweep.py and
follows it exactly in method -- an interval sweep of theta x s boxes, with the
derivatives taken ANALYTICALLY in s rather than by finite differences.  The
only structural difference is the factor ((s-1) zeta(s))^z, absent in the odd
case, which contributes z A(s) to log G_2 and is handled by the certified
Stieltjes expansion of beta_sweep.py.

STRUCTURE.  With a_p = p^-s, l_p = log p, A(s) = log((s-1) zeta(s)):

    G_2(s,z) = ((s-1) zeta(s))^z (1-2^-s)^z prod_{p>=3} (1-z a_p)^-1 (1-a_p)^z

    L   = z [ A + log(1-a_2) ]
          + sum_{p>=3} [ z log(1-a_p) - log(1-z a_p) ]
    L'  = z [ A' + l_2 a_2/(1-a_2) ]
          + sum_{p>=3} [ z l_p a_p/(1-a_p) - z l_p a_p/(1-z a_p) ]
    L'' = z [ A'' - l_2^2 a_2/(1-a_2)^2 ]
          + sum_{p>=3} [ -z l_p^2 a_p/(1-a_p)^2 + z l_p^2 a_p/(1-z a_p)^2 ]

    |G_2|        = exp(Re L)
    |d_s G_2|    = |G_2| |L'|
    |d_s^2 G_2| <= |G_2| (|L'|^2 + |L''|)

A, A' and A'' come from g(x) = (s-1) zeta(s) = 1 + sum_n (-1)^n gamma_n
x^{n+1}/n!, x = s-1, with certified Stieltjes constants (acb.stieltjes) and
the Berndt tail |gamma_n| <= (3+(-1)^n)(n-1)!/pi^n, i.e. |gamma_n/n!| <=
4/(n pi^n).  Then A = log g, A' = g'/g, A'' = (g'' g - g'^2)/g^2.

WHY THE PRIME SUM IS SPLIT IN TWO.  The two halves of each summand diverge
separately -- sum_p l_p a_p/(1-a_p) is a divergent sum -- and only their
DIFFERENCE is summable:

    z l_p a_p [ 1/(1-a_p) - 1/(1-z a_p) ] = z l_p a_p^2 (1-z)
                                            / ((1-a_p)(1-z a_p))     = O(l_p/p^2)
    z l_p^2 a_p [ 1/(1-z a_p)^2 - 1/(1-a_p)^2 ]
        = z l_p^2 a_p^2 (z-1)(2 - a_p(z+1))
          / ((1-a_p)^2 (1-z a_p)^2)                                  = O(l_p^2/p^2)

so primes above PEXACT are bounded in the CANCELLED form, uniformly in z on
the circle, once per s-box.  Bounding the halves separately would give an
infinite tail.  Primes below PEXACT are evaluated per (s, theta) box as
intervals, where the cancellation happens exactly.

Prime tails above PCUT use the same Rosser-Schoenfeld constants as
beta_sweep.py and mr_deriv_sweep.py: sum_{p>P} log p/p^2 <= 2.52/P and
sum_{p>P} (log p)^2/p^2 <= 2.52(log P + 1)/P.

SELF-TEST.  Before sweeping, the script evaluates G_2(1, R) from the formula
above on the degenerate box s = 1 and compares it with sum_i c_i R^i built
from ci_certified.json (head i <= 30) and tail_constants.json (tail, via
|c_i| <= rho/3^(i+1) + supH/4.2^i).  Those come from a different computation
entirely, so agreement ties this file's G_2 to a certified artifact.  If the
two intervals are disjoint the script refuses to report.

Usage: python3 m1_certified.py [NTHETA] [NS] [PEXACT] [PCUT] [PREC] [MAXDEPTH]
Setting of record:  python3 m1_certified.py 64 32 1000 100000 300 26
"""
import json
import os
import sys

from flint import acb, arb, ctx

NTHETA = int(sys.argv[1]) if len(sys.argv) > 1 else 64
NS     = int(sys.argv[2]) if len(sys.argv) > 2 else 32
PEXACT = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
PCUT   = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
PREC   = int(sys.argv[5]) if len(sys.argv) > 5 else 300
MAXDEPTH = int(sys.argv[6]) if len(sys.argv) > 6 else 26
# Relative tolerance for pruning.  A box is discarded once its upper bound is
# within TOL of a rigorous LOWER bound for the sup, and the reported bound is
# inflated by the same factor, so the result stays an upper bound.  Without it
# the search never terminates: the sup is attained at an interior point, so
# boxes around the maximiser can never be pruned against an exact lower bound
# and all of them run to MAXDEPTH.
TOL = 1e-3
ctx.prec = PREC

R      = arb("2.9")
RTEST  = arb(2)        # self-test radius; see ci_reference()
NGAMMA = 48

STORED_M1 = "2543.6624045073563"
STORED_M2 = "19881.155667290404"


class Straddle(Exception):
    """1 - z p^-s could not be separated from 0 on this box."""


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(3, n + 1) if s[i]]


def interval(lo, hi):
    return ((lo + hi) / 2).union(lo).union(hi)


def ball(r):
    """[-r, r] as an arb, for adding an explicit tail bound."""
    return interval(-r, r)


def cball(r):
    return acb(ball(r), ball(r))


# ---------------------------------------------------------------- Stieltjes

def stieltjes_coeffs():
    """c_n = (-1)^n gamma_n / n!, n <= NGAMMA, as certified arb balls."""
    out = []
    fac = arb(1)
    for n in range(NGAMMA + 1):
        if n > 0:
            fac *= n
        c = acb.stieltjes(n).real / fac
        out.append(-c if n % 2 else c)
    return out


def A_derivs(xbox, cs):
    """A = log g, A' = g'/g, A'' = (g'' g - g'^2)/g^2 on the x-box, x = s-1.

        g   = 1 + sum_n c_n x^(n+1)
        g'  =     sum_n c_n (n+1) x^n
        g'' =     sum_n c_n (n+1) n x^(n-1)
    """
    g, gp, gpp = arb(1), arb(0), arb(0)
    xpow = arb(1)                       # x^n
    xprev = arb(0)                      # x^(n-1), unused at n = 0
    for n in range(NGAMMA + 1):
        c = cs[n]
        g += c * xpow * xbox
        gp += c * (n + 1) * xpow
        if n >= 1:
            gpp += c * (n + 1) * n * xprev
        xprev = xpow
        xpow = xpow * xbox
    # Berndt tail, |c_n| <= 4/(n pi^n) for n > NGAMMA, |x| <= 1.  The extra
    # polynomial factors (n+1) and (n+1)n are absorbed crudely; pi^NGAMMA is
    # about 6e23, so any such slack is far below the working precision.
    pi = arb.pi()
    base = 4 / (pi ** NGAMMA * (1 - 1 / pi))
    g += ball(base / (NGAMMA + 1))
    gp += ball(base * 2)
    gpp += ball(base * 2 * (NGAMMA + 2) ** 2)
    if not (g > 0):
        sys.exit("g = (s-1)zeta(s) interval does not exclude 0 -- raise NS")
    return g.log(), gp / g, (gpp * g - gp * gp) / (g * g)


# ------------------------------------------------------------- the self-test

def ci_reference():
    """sum_i c_i R^i from ci_certified.json + tail_constants.json, as an arb.

    Returns None if either artifact is missing, so the sweep can still be run
    in a bare checkout -- but it then reports that the tie-in was skipped.
    """
    here = os.path.dirname(os.path.abspath(__file__))

    def load(name):
        for p in (os.path.join(here, name), name):
            if os.path.exists(p):
                return json.load(open(p))
        return None

    ci, tc = load("ci_certified.json"), load("tail_constants.json")
    if ci is None or tc is None:
        return None

    def parse(v):
        s = str(v).strip()
        if "+/-" in s:
            mid, rad = s.strip("[]").split("+/-")
            m, r = arb(mid.strip()), arb(rad.strip())
            return m.union(m - r).union(m + r)
        return arb(s)

    rho = parse(tc["rho"])
    supH = arb(str(tc["supH_R4.2_upper"]))
    tot = arb(0)
    for i in range(31):
        tot += parse(ci[str(i)]) * RTEST ** i
    # |c_i| <= |rho|/3^(i+1) + supH/4.2^i for i > 30
    r3, r4 = RTEST / 3, RTEST / arb("4.2")
    tail = abs(rho) / 3 * r3 ** 31 / (1 - r3) + supH * r4 ** 31 / (1 - r4)
    return tot + ball(tail)


# -------------------------------------------------------------------- sweep

def main():
    primes = sieve(PCUT)
    exact = [p for p in primes if p < PEXACT]
    bulk = [p for p in primes if p >= PEXACT]
    print("R=%.1f NTHETA=%d NS=%d PEXACT=%d (%d primes exact, %d bulk) "
          "PCUT=%d prec=%d  [s in [1,2]]"
          % (float(R), NTHETA, NS, PEXACT, len(exact), len(bulk), PCUT, PREC),
          flush=True)

    cs = stieltjes_coeffs()
    l2 = arb(2).log()

    # a_p, log p and log(1-a_p) depend only on the s-box, and s-boxes recur
    # across theta splits, so they are cached; likewise the bulk sums, which
    # are z-uniform.  Without this the 9424 bulk primes would be re-powered
    # on every one of the tens of thousands of box evaluations.
    _ecache, _bcache = {}, {}

    def key(b):
        return (str(b.lower()), str(b.upper()))

    def exact_data(sbox):
        k = key(sbox)
        if k not in _ecache:
            _ecache[k] = [(arb(q) ** (-sbox), arb(q).log(),
                           (1 - arb(q) ** (-sbox)).log()) for q in exact]
        return _ecache[k]

    # |z| over a theta-box rectangle exceeds R by at most a factor
    # sec(pi/NTHETA); Rmax is used in every z-uniform bulk/tail bound.
    Rmax = R / (arb.pi() / NTHETA).cos()
    print("Rmax over theta boxes = %.6f  (must stay < 3 for the p=3 factor)"
          % float(Rmax), flush=True)
    if not (Rmax < 3):
        sys.exit("theta boxes too wide: |z| reaches 3 and the p=3 Euler "
                 "factor loses its pole -- raise NTHETA")

    P = arb(PCUT)

    def tails(zmax):
        f = zmax * (zmax + 1) * arb("1.1") * arb("2.52")
        return (4 * zmax / (P * P.log()), f / P, f * (P.log() + 1) / P)

    _t = tails(Rmax)
    print("tails p>%d at |z|<=%.4f:  L %.3e   L' %.3e   L'' %.3e"
          % (PCUT, float(Rmax), float(_t[0]), float(_t[1]), float(_t[2])),
          flush=True)

    one = acb(1)

    def bulk_sums(sbox, zmax):
        k = (key(sbox), str(zmax))
        if k in _bcache:
            return _bcache[k]
        bL = bL1 = bL2 = arb(0)
        for q in bulk:
            ap = arb(q) ** (-sbox)
            lp = arb(q).log()
            d1 = 1 - ap
            dz = 1 - zmax * ap                 # <= |1 - z a_p|
            if not (dz > 0):
                sys.exit("bulk bound degenerate at p=%d" % q)
            bL += (zmax * ap * ap / d1 + (zmax * ap) ** 2 / dz) / 2
            bL1 += zmax * (zmax + 1) * lp * ap * ap / (d1 * dz)
            bL2 += (zmax * (zmax + 1) * lp * lp * ap * ap
                    * (2 + ap * (zmax + 1)) / (d1 * d1 * dz * dz))
        _bcache[k] = (bL, bL1, bL2)
        if len(_bcache) > 4000:
            _bcache.clear()
        return _bcache.get(k, (bL, bL1, bL2))

    def evaluate(sbox, z, zmax):
        """(Re L, L', L'') at one s-box and one z-box, as intervals.

        zmax is any upper bound for |z| on that box; it drives every
        z-uniform estimate below, so it must be an upper bound, not the
        nominal radius.
        """
        A, A1, A2 = A_derivs(sbox - 1, cs)
        a2 = arb(2) ** (-sbox)

        reL = (z * acb(A + (1 - a2).log())).real
        L1 = z * acb(A1 + l2 * a2 / (1 - a2))
        L2 = z * acb(A2 - l2 * l2 * a2 / ((1 - a2) * (1 - a2)))

        for ap, lp, l1p in exact_data(sbox):
            den = one - z * acb(ap)
            if not (abs(den) > 0):
                raise Straddle
            # NOTE: inv = 1/den, then inv*inv -- NOT 1/(den*den).  den is a
            # ball whose radius is comparable to its own modulus near the
            # p = 3 pole, so den*den straddles 0 there and the quotient blows
            # up by three orders of magnitude.  Squaring the inverse, which
            # is a ball bounded away from 0, is conditioned correctly.
            inv = one / den
            reL += (z * acb(l1p)).real - abs(den).log()
            L1 += z * acb(lp * ap / (1 - ap)) - z * acb(lp * ap) * inv
            L2 += (z * acb(-lp * lp * ap / ((1 - ap) * (1 - ap)))
                   + z * acb(lp * lp * ap) * inv * inv)

        bL, bL1, bL2 = bulk_sums(sbox, zmax)

        tl, t1, t2 = tails(zmax)
        reL += ball(bL + tl)
        L1 += cball(bL1 + t1)
        L2 += cball(bL2 + t2)
        return reL, L1, L2

    # ------------------------------------------------------------ self-test
    print("\nself-test: G_2(1, %.1f) from this file vs ci_certified.json"
          % float(RTEST))
    print("  (the tie-in radius is %.1f, not %.1f: at %.1f the certified c_i\n"
          "   tail (%.1f/3)^31/(1-%.1f/3) is about 10, so the reference there\n"
          "   is too wide to test anything)"
          % (float(RTEST), float(R), float(R), float(R), float(R)))
    s1 = arb(1)
    reL0, L10, L20 = evaluate(s1, acb(RTEST), RTEST)
    mine = reL0.exp()
    ref = ci_reference()
    if ref is None:
        print("  ci_certified.json / tail_constants.json not found -- "
              "TIE-IN SKIPPED")
    else:
        print("  this file  %s" % mine)
        print("  certified  %s" % ref)
        if not mine.overlaps(ref):
            sys.exit("SELF-TEST FAILED: the two intervals are disjoint; this "
                     "file's G_2 is not the certified one")
        print("  intervals overlap -- self-test passed")
    # invariant reference: the same quantities at s = 1 on the SWEEP circle
    r0, l1, l2_ = evaluate(s1, acb(R), R)
    h0 = r0.exp()
    at_s1 = (h0 * abs(l1), h0 * (abs(l1) * abs(l1) + abs(l2_)))
    print("  at s=1, z=%.1f:  |d_s G_2| <= %.4f   |d_s^2 G_2| <= %.4f"
          % (float(R), float(at_s1[0].upper()), float(at_s1[1].upper())))

    # ---------------------------------------------------------------- sweep
    #
    # Branch and bound for the sup, not a uniform grid.  A uniform grid has to
    # be fine enough for the worst box everywhere, and the worst box here is
    # the one at s = 1, theta = 0, where the p = 3 Euler factor has its pole
    # at |z| = 3 and the enclosure of 1 - z 3^-s is nearly as wide as it is
    # long.  Refining THERE and nowhere else is the difference between a bound
    # of 2.5e6 and a useful one.
    #
    # Validity does not depend on the search order: the boxes always cover
    # [1,2] x [0,2pi], so the reported value is max(best lower bound, sup of
    # the upper bounds of every box that survived).  Pruning only discards
    # boxes whose upper bound already falls below a rigorous lower bound for
    # the sup, which cannot remove the maximiser.

    def at_point(sv, tv):
        """Rigorous lower bounds for (|G_2|, |d_s G_2|, |d_s^2 G_2|)."""
        th = arb(tv)
        z = acb(th.cos(), th.sin()) * R
        reL, L1, L2 = evaluate(arb(sv), z, Rmax)
        H = reL.exp()
        return (H, H * abs(L1), H * (abs(L1) * abs(L1) + abs(L2)))

    def box_upper(slo, shi, tlo, thi):
        sbox = interval(slo, shi)
        th = interval(tlo, thi)
        z = acb(th.cos(), th.sin()) * R
        reL, L1, L2 = evaluate(sbox, z, Rmax)
        H = reL.exp()
        return (H, H * abs(L1), H * (abs(L1) * abs(L1) + abs(L2)))

    # seed the lower bound from the corner where the sup lives, plus a sample
    best_lo = [arb(0)] * 3
    # NOTE the 2*pi.  An earlier version seeded theta over [0,2] instead of
    # [0,2pi] and so never sampled theta = pi, which is exactly where the sup
    # of |d_s G_2| lives (z = -R).  A bad seed does not make the final bound
    # wrong -- every box is still covered -- but it destroys pruning and the
    # depth-first traversal can run for a long time reporting a partial
    # maximum that looks converged.
    tp = float(2 * arb.pi())
    seeds = [(1.0, 0.0), (1.0, tp / 2)] + [
        (1 + i / 8.0, tp * j / 16.0) for i in range(3) for j in range(17)]
    for sv, tv in seeds:
        try:
            v = at_point(sv, tv)
        except Straddle:
            continue
        for j in range(3):
            if float(v[j].lower()) > float(best_lo[j]):
                best_lo[j] = arb(float(v[j].lower()))
    print("\nseed lower bounds:  |G_2| >= %.2f  |d_s G_2| >= %.2f  "
          "|d_s^2 G_2| >= %.2f"
          % tuple(float(b) for b in best_lo), flush=True)

    two_pi = 2 * arb.pi()
    work = []
    for i in range(NS):
        for j in range(NTHETA):
            work.append((arb(1) + arb(i) / NS, arb(1) + arb(i + 1) / NS,
                         two_pi * j / NTHETA, two_pi * (j + 1) / NTHETA, 0))
    kept = [arb(0)] * 3
    nkept = nprune = nsplit = nstrad = 0
    while work:
        slo, shi, tlo, thi, d = work.pop()
        try:
            up = box_upper(slo, shi, tlo, thi)
        except Straddle:
            up = None
        if up is not None:
            for v in up:
                if not v.is_finite():
                    up = None
                    break
        if up is not None and all(
                float(up[j].upper()) <= float(best_lo[j]) * (1 + TOL)
                for j in range(3)):
            nprune += 1
            continue
        if up is not None and d >= MAXDEPTH:
            nkept += 1
            for j in range(3):
                u = arb(float(up[j].upper()))
                if float(u) > float(kept[j]):
                    kept[j] = u
            continue
        if up is None and d >= MAXDEPTH:
            sys.exit("box at depth %d still degenerate (s in [%s,%s]): raise "
                     "MAXDEPTH, NS or NTHETA" % (d, slo, shi))
        if up is None:
            nstrad += 1
        nsplit += 1
        # split the dimension that is wider relative to its own range
        sw = float((shi - slo).upper())
        tw = float((thi - tlo).upper()) / float(two_pi)
        if sw >= tw:
            mid = (slo + shi) / 2
            work.append((slo, mid, tlo, thi, d + 1))
            work.append((mid, shi, tlo, thi, d + 1))
            smid, tmid = mid, None
        else:
            mid = (tlo + thi) / 2
            work.append((slo, shi, tlo, mid, d + 1))
            work.append((slo, shi, mid, thi, d + 1))
            smid, tmid = None, mid
        # refresh the lower bound from the new interior point: a better lower
        # bound prunes more, and it costs one point evaluation
        if nsplit % 64 == 0:
            try:
                v = at_point(float(((slo + shi) / 2).mid()),
                             float(((tlo + thi) / 2).mid()))
                for j in range(3):
                    if float(v[j].lower()) > float(best_lo[j]):
                        best_lo[j] = arb(float(v[j].lower()))
            except Straddle:
                pass
        if (nkept + nprune) % 2000 == 0 and (nkept + nprune) > 0:
            print("  kept %d  pruned %d  split %d  queue %d   M1<=%.2f "
                  "M2<=%.2f  [PARTIAL]" % (nkept, nprune, nsplit, len(work),
                                max(float(kept[1]),
                                    float(best_lo[1]) * (1 + TOL)),
                                max(float(kept[2]),
                                    float(best_lo[2]) * (1 + TOL))),
                  file=sys.stderr, flush=True)

    worst = [arb(max(float(kept[j]), float(best_lo[j]) * (1 + TOL)))
             for j in range(3)]
    print("boxes: %d kept at full depth, %d pruned, %d splits (%d of them "
          "forced by\n       a degenerate enclosure near the p=3 pole)"
          % (nkept, nprune, nsplit, nstrad))

    M0, M1, M2 = (float(w) for w in worst)
    print()
    print("sup over |z| = %.1f, s in [1,2]:" % float(R))
    print("  |G_2|       <= %16.6f   (lower bound %.4f)"
          % (M0, float(best_lo[0])))
    print("  |d_s G_2|   <= %16.6f   (lower bound %.4f)"
          % (M1, float(best_lo[1])))
    print("  |d_s^2 G_2| <= %16.6f   (lower bound %.4f)"
          % (M2, float(best_lo[2])))
    print("  the gap between each pair is the remaining interval slack, not")
    print("  uncertainty about the true value: the sup lies between them.")
    print("  (upper bounds include the %.1e pruning tolerance.)" % TOL)

    # INVARIANT (beta_sweep.py's guard): the sup over boxes must dominate the
    # value at the degenerate box s = 1.  Its absence sank the v7 draft.
    print()
    ok_inv = (M1 >= float(at_s1[0].upper())
              and M2 >= float(at_s1[1].upper()))
    print("invariant sup >= value at s=1: %s" % ("PASS" if ok_inv else "FAIL"))
    if not ok_inv:
        sys.exit("INVARIANT VIOLATED -- the sweep is not covering s = 1")

    print()
    print("stored M1_R2.9    = %s" % STORED_M1)
    print("stored M2sup_R2.9 = %s" % STORED_M2)
    ok = True
    for nm, got, want in (("M1", M1, float(STORED_M1)),
                          ("M2sup", M2, float(STORED_M2))):
        print("  %-6s certified/stored = %.6f   %s"
              % (nm, got / want,
                 "stored value is JUSTIFIED (certified sup is below it)"
                 if got <= want else "*** STORED VALUE IS NOT AN UPPER "
                                     "BOUND ***"))
        ok = ok and got <= want
    print()
    if ok:
        print("verdict: both stored constants are certified upper bounds for "
              "the quantities\n         they are used as.  The trusted base "
              "no longer contains them on trust.")
    else:
        print("verdict: a STORED CONSTANT IS EXCEEDED by a certified lower "
              "bound on the sup.\n         Everything downstream of it is "
              "invalid until this is resolved.")
        sys.exit(1)


if __name__ == "__main__":
    main()
