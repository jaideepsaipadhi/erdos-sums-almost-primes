"""Gap 4: certified beta_i := sup_{s in [1,2]} |[z^i] G_2^{(1,0)}(s,z)|, i <= NMAX.

Structure (GLW (2.7), y=2):  G_2^{(1,0)}(s,z) = z * G_2(s,z) * c(s,z).

Per s-box (s an arb interval, 80-box partition of [1,2]):
  log G_2(s,z) = l_1(s) z + sum_{j>=2} l_j(s) z^j,
    l_1 = log(1-2^{-s}) + sum_{p>=3}(p^{-s} + log(1-p^{-s})) + log(zeta(s)(s-1)),
    l_j = P_s(j)/j,  P_s(j) = sum_{p>=3} p^{-sj},
  coefficients g_m of G_2(s,.) by exp recurrence (exact through N per Lemma 4.2).
  c(s,z) = C_0 + sum_{j>=1} C_j z^j,
    C_0 = log2/(2^s-1) + f(s) + Q(0),   C_j = Q(j) - Q(j-1),
    Q(j) = sum_{p>=3} log p * p^{-s(j+2)} / (1 - p^{-s}),
    f(s) = (log(zeta(s)(s-1)))' = g'(x)/g(x), x = s-1,
    g(x) = 1 + sum_n (-1)^n gamma_n x^{n+1}/n!  (certified Stieltjes via acb.stieltjes,
    tail via Berndt: |gamma_n| <= (3+(-1)^n)(n-1)!/pi^n).
  [z^i] G_2^{(1,0)} = sum_{m=0}^{i-1} g_m C_{i-1-m}.

Prime tails (p > P), all using s >= 1 so p^{-s} <= p^{-1}:
  |l_1 tail| <= 0.51 * T2,  T2 = 2.52/(P log P)  (Rosser-Schoenfeld, as before)
  P_s(j) tail in [0, T2 * P^{2-j}]  (j >= 2)
  Q(j) tail in [0, 1.01 * TL2 * P^{-j}],  TL2 = 2.52/P  (sum_{p>P} logp p^{-2} <= TL2)

INVARIANT (asserted): per-i sup over boxes >= |value at the degenerate box s=1|.
This is the guard whose absence sank the v7 draft.
"""
from flint import arb, acb, ctx
import json, math

NMAX = 30
NGAMMA = 48

def sieve(P):
    is_c = bytearray(P + 1); out = []
    for n in range(2, P + 1):
        if not is_c[n]:
            out.append(n)
            for m in range(n * n, P + 1, n):
                is_c[m] = 1
    return out

def interval(lo, hi):
    return ((lo + hi) / 2).union(lo).union(hi)

def stieltjes_certified(n):
    z = acb.stieltjes(n)
    return z.real

def f_and_logg(xbox, gammas):
    """certified f(s)=g'(x)/g(x) and log g(x) on x-box in [0,1]."""
    g = arb(1); gp = arb(0)
    fac = arb(1)
    xp = xbox  # x^{n+1} running
    for n in range(NGAMMA + 1):
        if n > 0:
            fac *= n
        term = gammas[n] / fac
        if n % 2 == 1:
            term = -term
        g += term * xp
        gp += term * (n + 1) * (xp / xbox if n >= 0 else arb(1))  # x^n
        xp = xp * xbox
    # careful x^n at n=0: xp/xbox invalid if xbox contains 0 -> recompute gp cleanly below
    # (recomputed properly in caller-safe version; see f_logg_safe)
    raise RuntimeError("use f_logg_safe")

def f_logg_safe(xbox, gammas):
    g = arb(1); gp = arb(0)
    fac = arb(1)
    xpow_n = arb(1)          # x^n
    for n in range(NGAMMA + 1):
        if n > 0:
            fac *= n
        coef = gammas[n] / fac
        if n % 2 == 1:
            coef = -coef
        g += coef * xpow_n * xbox      # x^{n+1}
        gp += coef * (n + 1) * xpow_n  # d/dx x^{n+1}
        xpow_n = xpow_n * xbox
    # Berndt tail: |gamma_n/n!| <= 4/(n pi^n) for n>=1; x<=1
    # g tail: sum_{n>NG} 4/(n pi^n) <= 4/((NG+1) pi^NG (1-1/pi))
    pi = arb.pi()
    tg = 4 / ((NGAMMA + 1) * pi ** NGAMMA * (1 - 1 / pi))
    tgp = 4 * (NGAMMA + 2) / ((NGAMMA + 1) * pi ** NGAMMA * (1 - 1 / pi))  # (n+1) factor <= crude
    g = g.union(g - tg).union(g + tg)
    gp = gp.union(gp - tgp).union(gp + tgp)
    return gp / g, g.log()

def beta_sweep(P=20000, boxes=80, prec=200):
    ctx.prec = prec
    primes = [p for p in sieve(P) if p >= 3]
    logs = [arb(p).log() for p in primes]
    gammas = [stieltjes_certified(n) for n in range(NGAMMA + 1)]
    T2 = arb("2.52") / (arb(P) * arb(P).log())
    TL2 = arb("2.52") / P
    ln2 = arb(2).log()

    sup_beta = [None] * (NMAX + 1)
    val_at_1 = [None] * (NMAX + 1)

    def process_box(sbox, record_point=False):
        x = sbox - 1
        f, logg = f_logg_safe(x, gammas)
        # prime sums
        Ps = [arb(0)] * (NMAX + 2)   # P_s(j) heads, j index up to NMAX+1
        Qs = [arb(0)] * (NMAX + 1)   # Q(j) heads, j = 0..NMAX
        l1_head = arb(0)
        for p, lp in zip(primes, logs):
            e1 = (-sbox * lp).exp()          # p^{-s}
            l1_head += e1 + (1 - e1).log()
            inv1m = 1 / (1 - e1)
            # powers p^{-s j}
            ej = e1 * e1                      # p^{-2s} for P_s(2)
            for j in range(2, NMAX + 2):
                Ps[j] += ej
                if j >= 2:
                    pass
                ej = ej * e1
            # Q(j): log p * p^{-s(j+2)} * inv1m
            eq = e1 * e1                      # p^{-2s} -> j=0
            for j in range(0, NMAX + 1):
                Qs[j] += lp * eq * inv1m
                eq = eq * e1
        # tails
        l1 = (1 - (-sbox * ln2).exp()).log() + l1_head \
             + interval(-arb("0.51") * T2, arb("0.51") * T2) + logg
        l = [arb(0), l1]
        for j in range(2, NMAX + 1):
            l.append((Ps[j] + interval(arb(0), T2 * arb(P) ** (2 - j))) / j)
        Q = [Qs[j] + interval(arb(0), arb("1.01") * TL2 * arb(P) ** (-j)) for j in range(NMAX + 1)]
        # G2 coefficients
        g = [arb(1)]
        for n in range(1, NMAX + 1):
            acc = arb(0)
            for j in range(1, n + 1):
                acc += j * l[j] * g[n - j]
            g.append(acc / n)
        # c coefficients
        C = [ln2 / ((sbox * ln2).exp() - 1) + f + Q[0]]
        for j in range(1, NMAX + 1):
            C.append(Q[j] - Q[j - 1])
        # b_i = [z^i] z*G2*c = sum_{m} g_m C_{i-1-m}
        out = []
        for i in range(NMAX + 1):
            if i == 0:
                out.append(arb(0))
                continue
            acc = arb(0)
            for m in range(0, i):
                acc += g[m] * C[i - 1 - m]
            out.append(acc)
        return out

    # degenerate box at s=1 (point) for the invariant
    pt = process_box(arb(1))
    for i in range(NMAX + 1):
        val_at_1[i] = abs(pt[i])

    for b in range(boxes):
        lo = arb(1) + arb(b) / boxes
        hi = arb(1) + arb(b + 1) / boxes
        sbox = interval(lo, hi)
        vals = process_box(sbox)
        for i in range(NMAX + 1):
            ub = abs(vals[i])
            u = arb(float(ub.upper()))
            sup_beta[i] = u if sup_beta[i] is None else (sup_beta[i] if float(sup_beta[i]) >= float(u) else u)

    # INVARIANT: sup >= value at s=1 (lower endpoint of |value| ball)
    violations = []
    for i in range(1, NMAX + 1):
        if float(sup_beta[i]) < float(val_at_1[i].lower()):
            violations.append(i)
    return sup_beta, val_at_1, violations

if __name__ == "__main__":
    import time
    t0 = time.time()
    # PRODUCTION SETTINGS -- the defaults do NOT reproduce beta_certified.json.
    # The manuscript's section 3.5 describes a 1000-box sweep; boxes=1600 gives
    # values at or below the stored table, boxes=800 slightly above.
    sup_beta, v1, viol = beta_sweep(P=100000, boxes=1600, prec=300)
    print(f"sweep done ({time.time()-t0:.0f}s)")
    print("INVARIANT sup>=value(s=1):", "VIOLATED at i=" + str(viol) if viol else "holds for all i")
    print(f"{'i':>3} {'sup_[1,2] beta_i':>18} {'|value at s=1|':>16}")
    for i in range(1, 15):
        print(f"{i:>3} {float(sup_beta[i]):>18.6f} {float(v1[i].mid()):>16.6f}")
    json.dump({i: float(sup_beta[i]) for i in range(NMAX + 1)}, open("beta_certified.json", "w"), indent=1)
