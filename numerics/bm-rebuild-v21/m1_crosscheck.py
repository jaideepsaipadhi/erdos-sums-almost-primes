#!/usr/bin/env python3
"""INDEPENDENT, NON-CERTIFIED cross-check of M1_R2.9 and M2sup_R2.9.

Those two constants sit in the trusted base (they bound the Cauchy tails of
beta_i and of the refined route) but no script in the repository produces
them.  This estimates them in double precision on a grid, by a different
route from anything in bm-rebuild-v21: it evaluates G_2 directly from

    G_2(s,z) = ((s-1) zeta(s))^z * H_o(s,z),
    log H_o  = z log(1-2^-s) + sum_{p>=3} [ -log(1-z p^-s) + z log(1-p^-s) ],

and differentiates in s by finite differences rather than by the analytic
formula, so a slip in the derivative algebra cannot be common to both.

It is a cross-check, not a certificate: double precision, a finite grid, and
primes truncated at PCUT.  A few agreeing digits corroborate; it proves
nothing.
"""
import sys
import numpy as np
from mpmath import mp, zeta as mpzeta, mpf

R      = 2.9
PCUT   = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
NS     = int(sys.argv[2]) if len(sys.argv) > 2 else 161
NTH    = int(sys.argv[3]) if len(sys.argv) > 3 else 256
H      = 1e-5
mp.dps = 30


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return np.array([i for i in range(3, n + 1) if s[i]], dtype=np.float64)


P = sieve(PCUT)
TH = np.linspace(0.0, 2.0 * np.pi, NTH, endpoint=False)
Z = R * np.exp(1j * TH)                      # (NTH,)


def A_of_s(s):
    """log((s-1) zeta(s)), continuous at s=1 with value 0."""
    if abs(s - 1.0) < 1e-13:
        return 0.0
    return float(mp.log(mpf(s - 1) * mpzeta(mpf(s))))


def G2(s):
    """G_2(s, z) on the whole contour, as a (NTH,) complex array."""
    a = P ** (-s)                            # (NP,)
    za = Z[:, None] * a[None, :]             # (NTH, NP)
    acc = (-np.log1p(-za)).sum(axis=1)
    acc = acc + Z * np.log1p(-a).sum()
    acc = acc + Z * np.log1p(-2.0 ** (-s))
    return np.exp(Z * A_of_s(s) + acc)


def selftest():
    """Validate this file's G_2 against the certified c_i before using it.

    c_i = [z^i] G_2(1,z), extracted here by FFT on |z|=R.  If these do not
    match ci_certified.json the rest of the output is meaningless.
    """
    import json, os
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "ci_certified.json")
    if not os.path.exists(path):
        path = "ci_certified.json"
    ref = json.load(open(path))
    global TH, Z
    TH_s, Z_s = TH, Z
    TH = np.linspace(0.0, 2.0 * np.pi, 4096, endpoint=False)
    Z = R * np.exp(1j * TH)
    coef = np.fft.fft(G2(1.0)) / 4096
    TH, Z = TH_s, Z_s
    worst = 0.0
    for i in range(8):
        v = ref.get(str(i))
        w = float(str(v).split("+/-")[0].strip(" []"))
        mine = (coef[i] / R ** i).real
        worst = max(worst, abs(mine - w))
        print("  c_%d  mine %18.10f   certified %18.10f" % (i, mine, w))
    print("  worst absolute deviation: %.2e" % worst)
    # absolute, not relative: ci_certified.json prints to ~10 decimals, so the
    # small coefficients carry only a few significant digits as stored.
    if worst > 1e-6:
        sys.exit("SELF-TEST FAILED: G_2 here does not match ci_certified.json")
    print("  self-test passed\n")


def main():
    print("R=%.2f primes<=%d (%d) NS=%d NTH=%d h=%g  [double precision]"
          % (R, PCUT, len(P), NS, NTH, H), flush=True)
    print("self-test against ci_certified.json:")
    selftest()
    best1 = (0.0, None)
    best2 = (0.0, None)
    for s in np.linspace(1.0, 2.0, NS):
        g0 = G2(s)
        gp = G2(s + H)
        gm = G2(s - H) if s - H >= 1.0 else None
        if gm is None:                        # one-sided at the left endpoint
            gpp = G2(s + 2 * H)
            d1 = (-3 * g0 + 4 * gp - gpp) / (2 * H)
            d2 = (g0 - 2 * gp + gpp) / (H * H)
        else:
            d1 = (gp - gm) / (2 * H)
            d2 = (gp - 2 * g0 + gm) / (H * H)
        m1 = float(np.abs(d1).max())
        m2 = float(np.abs(d2).max())
        if m1 > best1[0]:
            best1 = (m1, s)
        if m2 > best2[0]:
            best2 = (m2, s)
    print()
    print("sup |d_s   G_2| on |z|=%.1f, s in [1,2]  ~ %12.4f   at s = %.4f"
          % (R, best1[0], best1[1]))
    print("sup |d_s^2 G_2| on |z|=%.1f, s in [1,2]  ~ %12.4f   at s = %.4f"
          % (R, best2[0], best2[1]))
    print()
    print("stored M1_R2.9    = 2543.6624045073563")
    print("stored M2sup_R2.9 = 19881.155667290404")
    ok = True
    for nm, got, want in (("M1", best1[0], 2543.6624045073563),
                          ("M2sup", best2[0], 19881.155667290404)):
        print("  %-6s estimate/stored = %.4f %s"
              % (nm, got / want, "(stored is an upper bound)" if got <= want
                 else "*** STORED EXCEEDED ***"))
        ok = ok and got <= want
    print()
    print("verdict: " + ("both stored constants bound the estimated sup."
                        if ok else "a stored constant was EXCEEDED -- "
                        "investigate before trusting it."))


if __name__ == "__main__":
    main()
