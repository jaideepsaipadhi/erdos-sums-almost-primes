"""Assembly of the monotonicity criterion.

Crit(k) = a1*(k^2-2k-1) + 2E(k) - E(k+1)  > 0  <=>  f_{k+1} > f_k,
E(k) = -(log2/4)*(2k*U_k - V_k) - Delta(k) - E1(k) + Eexp(k),
  U_k = sum_{i<=k} i 2^i c_i,   V_k = sum_{i<=k} i^2 2^i c_i   (certified balls:
        head i<=30 exact-ball, 31..k via c_i in -rho/3^{i+1} +/- M/4.2^i),
  Delta(k) = certified convolution (delta_conv.py),
  Eexp(k) = 2^{k+1} w_k - (log2/4) k^2 W_k - 2^k T_k, with
        w_k = sum_{i>k} c_i,  W_k = sum_{i>k} 2^i c_i  (geometric tail balls),
        2^k T_k in [0, 1/(k log2 (1-2^-k))]  (s>=2 tail, GLW (2.9) chain, exact),
  E1(k) = 2^k (I_k - I'_k): |E1(k)| <= alpha*k + beta   *** PROVISIONAL ***
        (gap 4: certified b_i sweep pending; v7's alpha=15.374, beta=-37.226
         used as placeholder, clearly uncertified).
a1 = d log2/4 with certified d.

Worst-case: every ball at its adverse endpoint independently (valid lower bound
on Crit; conservative since sources may correlate favorably).
"""
from flint import arb, ctx
import json, re
from delta_conv import load_all, Delta

ALPHA, BETA = "15.374", "-37.226"   # PROVISIONAL (gap 4)

def crit_sweep(klo, khi, alpha=ALPHA, beta=BETA, prec=400):
    ctx.prec = prec
    ci, rho, supH, delta = load_all(prec)
    ln2 = arb(2).log()
    q = ln2 / 4
    from ci_certified import certified_d
    d = certified_d(2000000, prec)   # in-process certified d, no hardcoding
    a1 = d * q
    al, be = arb(alpha), arb(beta)

    def coeff_ball(i):
        if i <= 30:
            return ci[i]
        c = -rho / arb(3) ** (i + 1)
        h = supH / arb("4.2") ** i
        return c.union(c - h).union(c + h)

    # precompute partial sums U_k,V_k incrementally
    results = {}
    U = arb(0); V = arb(0)
    Uc = {}; Vc = {}
    for i in range(0, khi + 2):
        c = coeff_ball(i)
        t = arb(2) ** i * c
        U += i * t
        V += i * i * t
        Uc[i] = U; Vc[i] = V

    def tails(k):
        # w_k = sum_{i>k} c_i,  W_k = sum_{i>k} 2^i c_i, from (5.1) balls, closed geometric forms
        # principal: -rho * sum_{i>k} r^i/3  with r=1/3 (w) or 2/3 (W)
        r3 = arb(1) / 3
        w_main = -rho * r3 ** (k + 1) / (1 - r3) / 3 * 3  # -rho*sum_{i>k}3^{-i-1} = -rho*3^{-(k+1)}/(1-1/3)/1 ... compute directly:
        w_main = -rho * (arb(3) ** (-(k + 2))) / (1 - r3)
        w_err = supH * (arb("4.2") ** (-(k + 1))) / (1 - 1 / arb("4.2"))
        w = w_main.union(w_main - w_err).union(w_main + w_err)
        r23 = arb(2) / 3
        W_main = -rho / 3 * (r23 ** (k + 1)) / (1 - r23)
        rW = arb(2) / arb("4.2")
        W_err = supH * (rW ** (k + 1)) / (1 - rW)
        W = W_main.union(W_main - W_err).union(W_main + W_err)
        return w, W

    def Eexp_ball(k):
        w, W = tails(k)
        Tterm_hi = 1 / (k * ln2 * (1 - arb(2) ** (-k)))
        Tterm = (Tterm_hi / 2).union(arb(0)).union(Tterm_hi)  # 2^k T_k in [0, hi]
        return arb(2) ** (k + 1) * w - q * arb(k) ** 2 * W - Tterm

    def E_parts(k):
        # returns (certified part of E(k), i.e. everything except E1) as ball
        S3 = -q * (2 * k * Uc[k] - Vc[k])
        D = Delta(k, ci, rho, supH, delta)
        return S3 - D + Eexp_ball(k)

    Ep = {}
    for k in range(klo, khi + 1):
        if k not in Ep: Ep[k] = E_parts(k)
        if k + 1 not in Ep: Ep[k + 1] = E_parts(k + 1)
        certified = a1 * (arb(k) ** 2 - 2 * k - 1) + 2 * Ep[k] - Ep[k + 1]
        # E1 adverse: |2E1(k)-E1(k+1)| <= 2(al k+be) + (al (k+1)+be) = 3 al k + al + 3 be
        e1_adverse = 3 * al * k + al + 3 * be
        lower = certified - e1_adverse
        results[k] = (float(lower.lower()), float(certified.mid()), float(e1_adverse.mid()))
    return results

if __name__ == "__main__":
    res = crit_sweep(650, 899)
    fails = [k for k, (lo, _, _) in res.items() if lo <= 0]
    print(f"sweep k=650..899: {len(fails)} values with non-positive certified lower bound")
    if fails:
        print("failing k:", fails[:40], "..." if len(fails) > 40 else "")
        kstar = max(fails)
        print(f"largest failing k = {kstar}  =>  provisional crossing K0 = {kstar+1}")
    for k in [700, 720, 730, 735, 739, 740, 741, 742, 745, 750, 800, 850, 899]:
        lo, mid, e1 = res[k]
        print(f"k={k:4d}  crit_lower={lo:12.2f}   (certified part mid={mid:.1f}, E1 allowance={e1:.1f})")
    json.dump({k: v for k, v in res.items()}, open("/home/claude/crit_sweep.json", "w"))
