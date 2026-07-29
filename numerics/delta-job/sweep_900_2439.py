"""Certified criterion sweep k in [900,2439] with the FALLBACK E1 bound
(refined M2 would need an A2-table to 2440 for no benefit; margins here are
huge). Run inside bm-rebuild-v21/ AFTER merge_verify.py passes.
Prints the verdict + margin endpoints; writes crit_900_2439.json."""
from flint import arb, ctx
import json
from delta_conv import load_all, Delta
from ci_certified import certified_d

KLO, KHI = 900, 2439
prec = 400
ctx.prec = prec
ci, rho, supH, delta = load_all(prec)
beta = {int(k): arb(str(v)) for k, v in json.load(open('beta_certified.json')).items()}
M1 = arb(str(json.load(open('m1_constant.json'))['M1_R2.9']))
ln2 = arb(2).log(); q = ln2/4
d = certified_d(2000000, prec); a1 = d*q

def coeff_ball(i):
    if i <= 30: return ci[i]
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
    s = arb(0)
    for i in range(1, min(30, k)+1):
        s += beta[i]*arb(2)**i*(k+1-i)
    r = arb(2)/arb("2.9"); tail = arb(0); ri = r**31
    for i in range(31, k+1):
        tail += ri*(k+1-i); ri *= r
    return (s + M1*tail)/2

def Ep(k):
    return -q*(2*k*Uc[k] - Vc[k]) - Delta(k, ci, rho, supH, delta) + Eexp(k)

Ecache = {}; res = {}
for k in range(KLO, KHI+1):
    for kk in (k, k+1):
        if kk not in Ecache: Ecache[kk] = Ep(kk)
    crit = a1*(arb(k)**2-2*k-1) + 2*Ecache[k] - Ecache[k+1] - (2*E1b(k)+E1b(k+1))
    res[k] = float(crit.lower())
    if k % 200 == 0: print(f"k={k}: {res[k]:.1f}", flush=True)
fails = [k for k, v in res.items() if v <= 0]
json.dump(res, open("crit_900_2439.json", "w"))
print(f"\nsweep [900,2439]: {len(fails)} non-positive " + ("<- INVESTIGATE" if fails else ""))
print(f"endpoints: crit({KLO})={res[KLO]:.1f}, crit({KHI})={res[KHI]:.1f}")
print("VERDICT:", "ALL POSITIVE — range [900,2439] certified; joins [2440,inf)" if not fails else f"FAILURES at {fails[:20]}")
