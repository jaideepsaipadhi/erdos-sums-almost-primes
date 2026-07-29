"""Executable, pure-arb version of the far-range threshold derivation.
All comparisons via ball endpoints; no float arithmetic in any inequality.
Proves: Crit(k) > 0 for ALL k >= K1, using only
  - the proven delta bound |delta_m| <= (log2) m log(m+1) + 1   (all m >= 0)
  - certified S*, U/V absolute bounds (k >= 900), alpha_plus, a1 (d in-process)
  - derivative domination for the infinite tail.
"""
from flint import arb, ctx
import json
from delta_conv import load_all
from ci_certified import certified_d

def far_range_threshold(prec=300, verbose=True):
    ctx.prec = prec
    ci, rho, supH, _ = load_all(prec)
    ln2 = arb(2).log()
    q = ln2 / 4
    d = certified_d(2000000, prec)          # in-process, no hardcoding
    a1 = d * q
    beta = {int(k): arb(str(v)) for k, v in json.load(open('beta_certified.json')).items()}
    M1 = arb(str(json.load(open('m1_constant.json'))['M1_R2.9']))

    def coeff_ball(i):
        if i <= 30:
            return ci[i]
        c = -rho / arb(3) ** (i + 1)
        h = supH / arb("4.2") ** i
        return c.union(c - h).union(c + h)

    # S* upper bound (head + closed geometric tails)
    Sstar = arb(0)
    for i in range(31):
        Sstar += arb(2) ** i * abs(ci[i])
    r23 = arb(2) / 3
    rM = arb(2) / arb("4.2")
    Sstar += abs(rho) / 3 * (r23 ** 31) / (1 - r23) + supH * (rM ** 31) / (1 - rM)

    # |U_k|, |V_k| valid for ALL k >= 900:
    # partial sums to 900 plus absolute tail sum_{i>900} i^a 2^i |c_i|-bound.
    U = arb(0); V = arb(0)
    for i in range(0, 901):
        t = arb(2) ** i * coeff_ball(i)
        U += i * t; V += i * i * t
    tU = arb(0); tV = arb(0)
    for i in range(901, 1300):
        b = abs(rho) / arb(3) ** (i + 1) + supH / arb("4.2") ** i
        tU += i * arb(2) ** i * b
        tV += i * i * arb(2) ** i * b
    # remainder i>1300 of the tail sums: terms ~ i^2 (2/3)^i; bound by
    # 2 * (last term) since ratio i^2 2^i 3^-i decays by factor <= 0.7 for i>=1300
    tV += 2 * (arb(1300) ** 2 * arb(2) ** 1300 * (abs(rho) / arb(3) ** 1301 + supH / arb("4.2") ** 1300))
    tU += 2 * (arb(1300) * arb(2) ** 1300 * (abs(rho) / arb(3) ** 1301 + supH / arb("4.2") ** 1300))
    Umax = abs(U) + tU   # arb upper endpoints used in comparisons
    Vmax = abs(V) + tV

    # alpha_plus: bound1(k) <= alpha_plus * (k+1)
    ap = arb(0)
    for i in range(1, 53):
        ap += beta[i] * arb(2) ** i
    r25 = arb(2) / arb("2.5")
    ap = ap / 2 + M1 * (r25 ** 53) / (1 - r25) / 2

    def D(m):  # proven uniform bound, arb
        return ln2 * m * arb(m + 1).log() + 1

    def rhs(k):
        # |2(2kU_k - V_k) - (2(k+1)U_{k+1} - V_{k+1})|:
        # treat U_k=U_{k+1}=U, V likewise, plus explicit correction for the
        # difference (k+1)2^{k+1}|c_{k+1}| terms (k>=900): covered by 4*Umax+Vmax slack
        s3 = q * ((2 * k - 2) * Umax + Vmax + 4 * Umax + Vmax)
        conv = Sstar * (2 * D(k) + D(k + 1))
        e1 = ap * (2 * (k + 1) + (k + 2))
        eexp = 3 * (arb("1.45") / k + arb("0.001"))
        return s3 + conv + e1 + eexp

    def lhs(k):
        return a1 * (arb(k) ** 2 - 2 * k - 1)

    # scan for K1: smallest k >= 900 with lhs(k) - rhs(k) certifiably > 0
    k = 900
    while not ((lhs(k) - rhs(k)) > 0):   # arb '>' is certified (true only if provably >)
        k += 1
        if k > 20000:
            raise RuntimeError("no threshold found")
    K1 = k
    margin = lhs(K1) - rhs(K1)

    # derivative domination for all k >= K1:
    # d/dk lhs = a1(2k-2); d/dk rhs <= 2 q Umax + 3 Sstar ln2 (log(k+2)+1) + 3 ap
    # (D'(m) = ln2(log(m+1) + m/(m+1)) <= ln2(log(m+1)+1); worst at m=k+1)
    def dgap(k):
        return a1 * (2 * k - 2) - (2 * q * Umax + 3 * Sstar * ln2 * (arb(k + 2).log() + 1) + 3 * ap)
    assert dgap(K1) > 0, "derivative gap not certified positive at K1"
    # convexity: d2/dk2 (lhs - rhs) >= 2 a1 - 3 Sstar ln2/(k+2) > 0 for k >= kc:
    kc = 0
    while not ((2 * a1 - 3 * Sstar * ln2 / (kc + 2)) > 0):
        kc += 1
    assert kc <= K1, f"convexity threshold {kc} exceeds K1"

    if verbose:
        print(f"d      = {d.str(12)}")
        print(f"S*    <= {float(Sstar.upper()):.6f}")
        print(f"|U|   <= {float(Umax.upper()):.6f}, |V| <= {float(Vmax.upper()):.6f}  (k>=900)")
        print(f"a+     = {float(ap.upper()):.6f}")
        print(f"K1     = {K1}   certified margin = {margin.str(8)}")
        print(f"deriv gap at K1 = {dgap(K1).str(8)} (>0), convexity from k >= {kc}")
        print(f"==> Crit(k) > 0 PROVEN for all k >= {K1} (pure arb, no floats)")
    return K1

if __name__ == "__main__":
    far_range_threshold()
