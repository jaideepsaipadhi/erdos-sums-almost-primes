"""Refined criterion sweep: E1(k) enclosed as M2(k) +/- Gamma (signed main term
+ certified k-independent remainder). PROVISIONAL until the his-box acceptance
gate (|implied E1 - M2| <= Gamma at all certificate points) passes.
Old bound & K0=735 remain the proven fallback; this is additive."""
from flint import arb, ctx
import json, re, sys, time
from delta_conv import load_all, Delta
from ci_certified import certified_d
from s2_table import A2

def parse(s):
    m = re.match(r"\[?(-?[0-9.]+(?:e[+-]?[0-9]+)?)(?: \+/- ([0-9.e+-]+))?\]?", s)
    a = arb(m.group(1)); r = arb(m.group(2) or "0")
    return a.union(a-r).union(a+r)

def sweep(klo, khi, prec=400):
    ctx.prec = prec
    ci, rho, supH, delta = load_all(prec)
    ln2 = arb(2).log(); q = ln2/4
    d = certified_d(2000000, prec)
    a1 = d*q
    bhat = {int(k): parse(v) for k, v in json.load(open('bhat_signed_N60.json')).items()}
    gc = json.load(open('gamma_constant.json'))
    Gamma = arb(str(gc["Gamma"]))
    M1 = arb(str(json.load(open('m1_constant.json'))['M1_R2.9']))

    def coeff_ball(i):
        if i <= 30: return ci[i]
        c = -rho/arb(3)**(i+1); h = supH/arb("4.2")**i
        return c.union(c-h).union(c+h)

    U = arb(0); V = arb(0); Uc = {}; Vc = {}
    for i in range(0, khi+2):
        t = arb(2)**i * coeff_ball(i)
        U += i*t; V += i*i*t
        Uc[i] = U; Vc[i] = V

    A2cache = {}
    def A2c(m):
        if m not in A2cache: A2cache[m] = A2(m, int(1.6*m)+200)
        return A2cache[m]

    def M2(k):
        s = arb(0)
        for i in range(1, min(60, k)+1):
            s += bhat[i] * arb(2)**i * A2c(k-i)
        r = arb(2)/arb("2.9")
        tail = M1 * (r**61)/(1-r) * (arb(k+1)/2)
        return s.union(s - tail).union(s + tail)

    def E1ball(k):
        m2 = M2(k)
        return m2.union(m2 - Gamma).union(m2 + Gamma)

    def tails(k):
        r3 = arb(1)/3
        w_main = -rho*(arb(3)**(-(k+2)))/(1-r3)
        w_err = supH*(arb("4.2")**(-(k+1)))/(1-1/arb("4.2"))
        w = w_main.union(w_main-w_err).union(w_main+w_err)
        r23 = arb(2)/3
        W_main = -rho/3*(r23**(k+1))/(1-r23)
        rW = arb(2)/arb("4.2")
        W_err = supH*(rW**(k+1))/(1-rW)
        W = W_main.union(W_main-W_err).union(W_main+W_err)
        return w, W

    def Eexp(k):
        w, W = tails(k)
        hi = 1/(k*ln2*(1-arb(2)**(-k)))
        T = (hi/2).union(arb(0)).union(hi)
        return arb(2)**(k+1)*w - q*arb(k)**2*W - T

    def E(k):
        return -q*(2*k*Uc[k] - Vc[k]) - Delta(k, ci, rho, supH, delta) - E1ball(k) + Eexp(k)

    Ek = {}; res = {}
    t0 = time.time()
    for k in range(klo, khi+1):
        for kk in (k, k+1):
            if kk not in Ek: Ek[kk] = E(kk)
        crit = a1*(arb(k)**2 - 2*k - 1) + 2*Ek[k] - Ek[k+1]
        res[k] = float(crit.lower())
        if k % 100 == 0: print(f"  k={k} ({time.time()-t0:.0f}s)", flush=True)
    return res

if __name__ == "__main__":
    klo, khi = int(sys.argv[1]), int(sys.argv[2])
    res = sweep(klo, khi)
    fails = sorted(k for k, v in res.items() if v <= 0)
    print(f"sweep [{klo},{khi}]: {len(fails)} non-positive")
    if fails:
        print("largest failing k =", fails[-1], " contiguous:",
              fails == list(range(fails[0], fails[-1]+1)))
    out = {}
    if len(sys.argv) > 3:
        json.dump(res, open(sys.argv[3], "w"))
    for k in sorted(res)[:0]: pass
    ks = sorted(res)
    show = [k for k in ks if (fails and abs(k - fails[-1]) <= 2) or k in (ks[0], ks[-1])]
    for k in show:
        print(f"  k={k}: crit_lower = {res[k]:.2f}")
