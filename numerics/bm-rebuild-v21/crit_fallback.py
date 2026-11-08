"""Certified criterion sweep over any range, with the FALLBACK E1 bound.

This is sweep_900_2439.py generalized to an arbitrary [klo,khi], and it exists
to give `crit_certified.json`'s slice a generator that uses only inputs the
manuscript states.

    Crit(k) = a1*(k^2-2k-1) + 2E(k) - E(k+1) - (2*E1b(k) + E1b(k+1)) > 0
              <=>  f_{k+1} > f_k,

with E(k) = -(log2/4)(2k*U_k - V_k) - Delta(k) + Eexp(k) exactly as in
crit_assembly.py's docstring, and E1b the FALLBACK bound on E1 built per-i from
`beta_certified.json` plus the `M1` tail at R = 2.9 -- the same bound
sweep_900_2439.py uses for [900,2439].

WHY THIS SCRIPT EXISTS.  `crit_certified.json` covers [650,899] and is
load-bearing: it is the only artifact covering 735..899, the slice between
crit_refined.py's [78,734] and sweep_900_2439.py's [900,2439].  It was NOT
produced by either, nor by crit_assembly.py as committed.  Solving for the
inputs that reproduce it gives

    |E1(k)| <= alpha*k + beta    with   alpha = 15.5716454,  beta = -39.60918

(the combination the criterion sees is alpha*(3k+1) + 3*beta, per
crit_assembly.py's own comment; the fit is exact at k = 650, 735 and 899).
That alpha is the manuscript's SUPERSEDED value -- the paper now states
alpha_+ <= 15.425661 -- and that beta is a NEGATIVE intercept, which tightens
the bound and appears nowhere in the manuscript's certified inputs.  So the
file is not reproducible from the paper's stated constants, and its margin at
k = 735 is only 43.0.

The fallback bound used here needs no beta at all and is tighter than either
linear form, because it keeps the per-i structure instead of enveloping it.  At
k = 735 it gives 362.6 against the old file's 43.0.  Nothing in the manuscript
has to change: alpha_+ <= 15.425661 is exactly the linear envelope of this
bound, and is reported below as a cross-check against uv_constants.json.

Run inside bm-rebuild-v21/.

    python3 crit_fallback.py 650 899 crit_650_899.json    # -> crit_650_899.log
    python3 crit_fallback.py 900 2439 /tmp/regress.json   # must equal
                                                          # crit_900_2439.json

The second is the regression test: this script must reproduce
sweep_900_2439.py's committed output bit for bit, since on that range the two
compute the same quantity by the same route.
"""
from flint import arb, ctx
import json
import sys

KLO = int(sys.argv[1]) if len(sys.argv) > 1 else 650
KHI = int(sys.argv[2]) if len(sys.argv) > 2 else 899
OUT = sys.argv[3] if len(sys.argv) > 3 else None

from delta_conv import load_all, Delta
from ci_certified import certified_d

prec = 400
ctx.prec = prec
ci, rho, supH, delta = load_all(prec)
beta = {int(k): arb(str(v)) for k, v in json.load(open('beta_certified.json')).items()}
M1 = arb(str(json.load(open('m1_constant.json'))['M1_R2.9']))
ln2 = arb(2).log(); q = ln2/4
d = certified_d(2000000, prec); a1 = d*q


def coeff_ball(i):
    if i <= 30:
        return ci[i]
    c = -rho/arb(3)**(i+1); h = supH/arb("4.2")**i
    return c.union(c-h).union(c+h)


U = arb(0); V = arb(0); Uc = {}; Vc = {}
for i in range(0, KHI+2):
    t = arb(2)**i * coeff_ball(i)
    U += i*t; V += i*i*t
    Uc[i] = U; Vc[i] = V


def tails(k):
    r3 = arb(1)/3
    w_m = -rho*(arb(3)**(-(k+2)))/(1-r3)
    w_e = supH*(arb("4.2")**(-(k+1)))/(1-1/arb("4.2"))
    w = w_m.union(w_m-w_e).union(w_m+w_e)
    r23 = arb(2)/3
    W_m = -rho/3*(r23**(k+1))/(1-r23)
    rW = arb(2)/arb("4.2")
    W_e = supH*(rW**(k+1))/(1-rW)
    return w, W_m.union(W_m-W_e).union(W_m+W_e)


def Eexp(k):
    w, W = tails(k)
    hi = 1/(k*ln2*(1-arb(2)**(-k)))
    return arb(2)**(k+1)*w - q*arb(k)**2*W - (hi/2).union(arb(0)).union(hi)


def E1b(k):
    """FALLBACK bound on E1(k), per-i from the certified beta_i plus M1 tail."""
    s = arb(0)
    for i in range(1, min(30, k)+1):
        s += beta[i]*arb(2)**i*(k+1-i)
    r = arb(2)/arb("2.9"); tail = arb(0); ri = r**31
    for i in range(31, k+1):
        tail += ri*(k+1-i); ri *= r
    return (s + M1*tail)/2


def Ep(k):
    return -q*(2*k*Uc[k] - Vc[k]) - Delta(k, ci, rho, supH, delta) + Eexp(k)


# alpha_+ is the linear envelope of E1b: report it against uv_constants.json
r = arb(2)/arb("2.9")
alpha_env = sum((beta[i]*arb(2)**i for i in range(1, 31)), arb(0))/2 \
    + M1*(r**31/(1-r))/2
try:
    alpha_pub = json.load(open('uv_constants.json'))["alpha_plus"]
except Exception:
    alpha_pub = None
print(f"alpha_+ envelope of E1b (in-process) = {alpha_env.str(12)}")
print(f"alpha_+ in uv_constants.json         = {alpha_pub}"
      + ("  [consistent]" if alpha_pub is not None
         and arb(str(alpha_pub)) >= alpha_env else "  [CHECK]"))

Ecache = {}; res = {}
for k in range(KLO, KHI+1):
    for kk in (k, k+1):
        if kk not in Ecache:
            Ecache[kk] = Ep(kk)
    crit = a1*(arb(k)**2-2*k-1) + 2*Ecache[k] - Ecache[k+1] - (2*E1b(k)+E1b(k+1))
    res[k] = float(crit.lower())
    if k % 200 == 0:
        print(f"k={k}: {res[k]:.1f}", flush=True)

fails = sorted(k for k, v in res.items() if v <= 0)
pos = sorted(k for k, v in res.items() if v > 0)
if OUT:
    json.dump(res, open(OUT, "w"))
print(f"\nsweep [{KLO},{KHI}]: {len(fails)} non-positive")
if pos:
    contig = pos == list(range(pos[0], pos[-1]+1))
    print(f"first positive k = {pos[0]}   positive block contiguous: {contig}")
    print(f"min over positive block = {min(res[k] for k in pos):.4f}"
          f"  (at k = {min(pos, key=lambda k: res[k])})")
if fails:
    print(f"non-positive k: [{fails[0]},{fails[-1]}]  contiguous: "
          f"{fails == list(range(fails[0], fails[-1]+1))}")
print(f"endpoints: crit({KLO})={res[KLO]:.4f}, crit({KHI})={res[KHI]:.4f}")
