"""gamma2_sweep.py — certified gamma-hat_i := sup_{s in [1,2]} |[z^i] G2^{(2,0)}(s,z)|.

GLW (2.29) at y=2:  G2^{(2,0)}(s,z) = G2(s,z) * ( z^2 c(s,z)^2 + z * c'(s,z) ),
c(s,z) as in beta_sweep;  c' = d/ds c has series  C'_0 + sum_{j>=1}(Q'_j - Q'_{j-1}) z^j,
  C'_0 = -(log2)^2 2^s/(2^s-1)^2 + f'(s) + Q'_0,
  Q'_j = -sum_{p>=3} (logp)^2 p^{-s(j+2)} [ (j+2)/(1-p^{-s}) + p^{-s}/(1-p^{-s})^2 ],
  f'(s) = g''/g - (g'/g)^2,  g(x)=1+sum (-1)^n gamma_n x^{n+1}/n!,  x=s-1.

Prime tails (p > P, s >= 1), all chained from
  TL2b := sum_{p>P} (logp)^2 p^{-2} <= 2.52 * logP / P
(Rosser-Schoenfeld partial summation: int_P^inf (logt)^2 t^{-2} dpi(t)
 <= 2.52 int_P^inf (logt - 1) t^{-2} dt * ... = 2.52 logP/P; boundary term <= 0 discarded):
  |Q'_j tail| <= 1.02*(j+3) * TL2b * P^{-j}.
Stieltjes tails: |gamma_n/n!| <= 4/(n pi^n) (Berndt), so
  g'' tail <= 8*(NG+2)*pi^{-NG}/(1-1/pi)   (conservative).

Composition: [z^i] G2^{(2,0)} = sum_m g_m * D_{i-m},
  D_r = [z^r](z^2 c^2 + z c') = sum_{u+v=r-2} C_u C_v + C'_{r-1}.
"""
from flint import arb, ctx
from beta_sweep import sieve, interval, stieltjes_certified
import beta_sweep as BS
import json, math

NM = 24

def f_f1_logg(xbox, gammas, NG):
    """certified (f, f', log g) on the x-box."""
    g = arb(1); gp = arb(0); gpp = arb(0)
    fac = arb(1); xn = arb(1)          # x^n
    xnm1 = None                        # x^{n-1}
    for n in range(NG + 1):
        if n > 0:
            fac *= n
        coef = gammas[n] / fac
        if n % 2 == 1:
            coef = -coef
        g += coef * xn * xbox
        gp += coef * (n + 1) * xn
        if n >= 1:
            gpp += coef * (n + 1) * n * xnm1
        xnm1 = xn
        xn = xn * xbox
    pi = arb.pi()
    tg = 4 / ((NG + 1) * pi ** NG * (1 - 1 / pi))
    tgp = 4 * (NG + 2) / ((NG + 1) * pi ** NG * (1 - 1 / pi))
    tgpp = 8 * (NG + 2) / (pi ** NG * (1 - 1 / pi))
    g = g.union(g - tg).union(g + tg)
    gp = gp.union(gp - tgp).union(gp + tgp)
    gpp = gpp.union(gpp - tgpp).union(gpp + tgpp)
    f = gp / g
    return f, gpp / g - f * f, g.log()

def process_box(sbox, primes, logs, gammas, T2, TL2, TL2b, P, prec):
    ctx.prec = prec
    ln2 = arb(2).log()
    f, f1, logg = f_f1_logg(sbox - 1, gammas, BS.NGAMMA)
    Ps = [arb(0)] * (NM + 2)
    Qs = [arb(0)] * (NM + 1)
    Qps = [arb(0)] * (NM + 1)
    l1_head = arb(0)
    for p, lp in zip(primes, logs):
        e1 = (-sbox * lp).exp()
        l1_head += e1 + (1 - e1).log()
        inv1m = 1 / (1 - e1)
        inv1m2 = inv1m * inv1m
        ej = e1 * e1
        for j in range(2, NM + 2):
            Ps[j] += ej; ej = ej * e1
        eq = e1 * e1
        lp2 = lp * lp
        for j in range(0, NM + 1):
            Qs[j] += lp * eq * inv1m
            Qps[j] += -lp2 * eq * ((j + 2) * inv1m + e1 * inv1m2)
            eq = eq * e1
    l1 = (1 - (-sbox * ln2).exp()).log() + l1_head \
         + interval(-arb("0.51") * T2, arb("0.51") * T2) + logg
    l = [arb(0), l1]
    for j in range(2, NM + 1):
        l.append((Ps[j] + interval(arb(0), T2 * arb(P) ** (2 - j))) / j)
    Q = [Qs[j] + interval(arb(0), arb("1.01") * TL2 * arb(P) ** (-j)) for j in range(NM + 1)]
    Qp = [Qps[j] + interval(-arb("1.02") * (j + 3) * TL2b * arb(P) ** (-j),
                            arb("1.02") * (j + 3) * TL2b * arb(P) ** (-j)) for j in range(NM + 1)]
    # G2 coefficients
    g = [arb(1)]
    for n in range(1, NM + 1):
        acc = arb(0)
        for j in range(1, n + 1):
            acc += j * l[j] * g[n - j]
        g.append(acc / n)
    # c and c' coefficients
    twos = (sbox * ln2).exp()
    C = [ln2 / (twos - 1) + f + Q[0]]
    Cp = [-(ln2 * ln2) * twos / (twos - 1) ** 2 + f1 + Qp[0]]
    for j in range(1, NM + 1):
        C.append(Q[j] - Q[j - 1])
        Cp.append(Qp[j] - Qp[j - 1])
    # D_r = sum_{u+v=r-2} C_u C_v + C'_{r-1}
    out = []
    for i in range(NM + 1):
        acc = arb(0)
        # G2 * D convolution: [z^i] = sum_{m=0}^{i} g_m D_{i-m}
        for m in range(0, i + 1):
            r = i - m
            Dr = arb(0)
            if r >= 2:
                for u in range(0, r - 1):
                    v = r - 2 - u
                    if v <= NM and u <= NM:
                        Dr += C[u] * C[v]
            if 1 <= r and r - 1 <= NM:
                Dr += Cp[r - 1]
            acc += g[m] * Dr
        out.append(acc)
    return out

# PRODUCTION SETTINGS: the old defaults (P=20000, boxes=200, prec=200) do not
# reproduce gamma2_certified.json -- they give head 228.46 vs the stored 204.89,
# which pushes Gamma to 117.19, above the 105.41 the criterion assumes.
# P=100000, boxes=800, prec=300 gives head 203.12, at or below the stored table.
def gamma2_sweep(P=100000, boxes=800, prec=300):
    ctx.prec = prec
    primes = [p for p in sieve(P) if p >= 3]
    logs = [arb(p).log() for p in primes]
    gammas = [stieltjes_certified(n) for n in range(BS.NGAMMA + 1)]
    T2 = arb("2.52") / (arb(P) * arb(P).log())
    TL2 = arb("2.52") / P
    TL2b = arb("2.52") * arb(P).log() / P
    pt = process_box(arb(1), primes, logs, gammas, T2, TL2, TL2b, P, prec)
    sup = [None] * (NM + 1)
    for b in range(boxes):
        sbox = interval(1 + arb(b) / boxes, 1 + arb(b + 1) / boxes)
        vals = process_box(sbox, primes, logs, gammas, T2, TL2, TL2b, P, prec)
        for i in range(NM + 1):
            ub = arb(float(abs(vals[i]).upper()))
            sup[i] = ub if sup[i] is None else (sup[i] if float(sup[i]) >= float(ub) else ub)
    viol = [i for i in range(NM + 1) if float(sup[i]) < float(abs(pt[i]).lower())]
    return sup, pt, viol

if __name__ == "__main__":
    import time
    t0 = time.time()
    sup, pt, viol = gamma2_sweep()
    print(f"sweep ({time.time()-t0:.0f}s); invariant sup>=|s=1|:",
          "VIOLATED at " + str(viol) if viol else "holds")
    for i in range(1, 10):
        print(f"i={i:2d}  gamma-hat_i = {float(sup[i]):.6f}   |value s=1| = {float(abs(pt[i]).mid()):.6f}")
    json.dump({i: float(sup[i]) for i in range(NM + 1)}, open("gamma2_certified.json", "w"), indent=1)
    json.dump({i: pt[i].str(20) for i in range(NM + 1)}, open("gamma2_s1_signed.json", "w"), indent=1)
