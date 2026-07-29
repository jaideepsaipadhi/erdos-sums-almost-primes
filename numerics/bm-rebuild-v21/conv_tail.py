"""Certified Delta(k) = sum_{i=0}^k 2^i c_i delta_{k-i}.

Head i <= N: certified c_i balls (ci_certified.py).
Tail i > N:  c_i = -rho/3^{i+1} + h_i,  |h_i| <= supH / R^i  (R = 4.2),
  rho = res_{z=3} G_2(1,z) = -(1/9) prod_{p>=5} (1-3/p)^{-1} (1-1/p)^3,
  H(z) = G_2(1,z) - rho/(z-3), holomorphic in |z| < 5,
  supH = certified sup of |H| on |z| = R via arc evaluation in acb.
delta_{k-i}: certified table (delta_table.jsonl), m = 0..900.

All prime tails use Sum_{p>P} p^-2 <= 2.52/(P log P)  (Rosser-Schoenfeld
pi(x) < 1.26 x / log x, x >= 17), chained: Sum_{p>P} p^-j <= tailP2 * P^{2-j}.
"""
from flint import arb, acb, ctx
import json, math

def sieve(P):
    is_c = bytearray(P + 1)
    out = []
    for n in range(2, P + 1):
        if not is_c[n]:
            out.append(n)
            for m in range(n * n, P + 1, n):
                is_c[m] = 1
    return out

def interval(lo, hi):
    return ((lo + hi) / 2).union(lo).union(hi)

def certified_rho(P, prec):
    """rho = -(1/9) prod_{p>=5} (1-3/p)^{-1} (1-1/p)^3, log terms sum_j (3^j-3)/(j p^j).
    Tail p > P: sum over j >= 2 of (3^j-3)/(j p^j) <= (3/p^2)(1 + 4/p + ...) <= 3.2/p^2 for p >= 100."""
    ctx.prec = prec
    primes = [p for p in sieve(P) if p >= 5]
    s = arb(0)
    for p in primes:
        pp = arb(p)
        s += -(1 - 3 / pp).log() + 3 * (1 - 1 / pp).log()
    tailP2 = arb("2.52") / (arb(P) * arb(P).log())
    tail = arb("3.2") * tailP2
    return -(interval(s - tail, s + tail)).exp() / 9

def G2_acb(z, primes, tP, ln2):
    """G_2(1,z) on an acb box z. Head: literal product over p<=Pc (p>2).
    Tail: sum_{j>=2} (z^j - z) tP[j] / j with certified tP balls."""
    acc = -z * ln2
    for p in primes:
        acc += -(1 - z / p).log() + z * (arb(1) - arb(1) / p).log()
    for j, t in tP.items():
        acc += (z ** j - z) * t / j
    return acc.exp()

def certified_supH(R, P, prec, arcs=240):
    ctx.prec = prec
    primes = [p for p in sieve(P) if p > 2]
    ln2 = arb(2).log()
    tailP2 = arb("2.52") / (arb(P) * arb(P).log())
    jmax = 40
    # tail-only prime zeta: tP[j] = sum_{p>P} p^-j (head primes are in the product!)
    tP = {}
    for j in range(2, jmax):
        tP[j] = interval(arb(0), tailP2 * arb(P) ** (2 - j))
    # tail-of-tail j >= jmax: |sum| <= sum_j R^j tailP2 P^{2-j} <= tailP2 P^2 (R/P)^{jmax}/(1-R/P)
    tt = tailP2 * arb(P) ** 2 * (arb(R) / P) ** jmax * 2
    rho = certified_rho(200000, prec)
    sup = arb(0)
    two_pi = 2 * arb.pi()
    # entire part: exp(-z ln2 + z * sum_p log(1-1/p) + tail(z)); pole factors as product
    S1r = arb(0)
    for p in primes:
        S1r += (arb(1) - arb(1) / p).log()
    sup = None
    for a in range(arcs):
        theta = interval(two_pi * a / arcs, two_pi * (a + 1) / arcs)
        z = acb(arb(R) * theta.cos(), arb(R) * theta.sin())
        acc = -z * ln2 + z * S1r
        for j, t in tP.items():
            acc += (z ** j - z) * t / j
        acc += acb(interval(-tt, tt), interval(-tt, tt))
        E = acc.exp()
        for p in primes:
            E = E / (1 - z / p)
        H = E - rho / (z - 3)
        ub = arb(H.abs_upper())
        sup = ub if sup is None else sup.union(ub)
    return sup, rho

if __name__ == "__main__":
    import time
    t0 = time.time()
    prec = 350
    rho = certified_rho(2000000, prec)
    print("rho =", rho.str(15), "  (prior indep. value: -0.174930743476)")
    sup, _ = certified_supH(R=4.2, P=10000, prec=250, arcs=240)
    print("sup|H| on |z|=4.2 <=", sup.str(8), f"  ({time.time()-t0:.0f}s)")
    json.dump({"rho": rho.str(20), "supH_R4.2_upper": str(float(sup.mid()) + float(sup.rad()))},
              open("/home/claude/tail_constants.json", "w"), indent=1)
