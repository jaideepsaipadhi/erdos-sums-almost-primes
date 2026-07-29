"""
CERTIFIED computation of f(N_k) = int_1^inf P_k(s) ds  (and squarefree analogue).

Every output is a rigorous enclosure [mid +/- rad] accounting for:
  (A) arithmetic error            -- arb ball arithmetic throughout
  (B) Mobius-series truncation    -- explicit error balls in prime_zeta
  (C) GL discretization error     -- per-panel Bernstein-ellipse bound
                                     (Trefethen, ATAP Thm 19.3 form, x10 safety)
  (D) node/weight inexactness     -- interval-Newton certified node balls
  (E) tail s >= S0                -- P(s) <= 2.78*2^-s (s>=2) => P_k <= 2.78^k 2^-ks
  (F) tail s -> 1+ (u > UHI)      -- Lichtman Lemma 5.6 + Gamma(k+1,UHI)/k! <= 2 UHI^k e^-UHI/k!
                                     (requires UHI >= 2k+2; we use UHI = 3.5*KMAX)

Usage: python3 certified.py KMAX PREC [p0 p1]   (panel range optional, for chunking)
"""
import numpy as np
from flint import acb, arb, ctx
import time, sys, os

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 300
ctx.prec = PREC
import flint
EPS_TINY = 2.0**(-(PREC//2))  # branch crossover: direct width ~2^-PREC/eps, sandwich width ~eps

ULO   = -5.10
UHI   = 3.5 * KMAX
H     = 0.8                    # panel width
NGL   = 52                     # GL points per panel
DELTA = 1.45                   # ellipse semi-minor in u units (< pi/2)
NPANEL = int(np.ceil((UHI - ULO) / H))
EDGES  = np.linspace(ULO, ULO + NPANEL * H, NPANEL + 1)

# ---------------- Mobius sieve ----------------
def mobius_sieve(n):
    mu=[1]*(n+1); comp=[False]*(n+1); pr=[]
    for i in range(2,n+1):
        if not comp[i]: pr.append(i); mu[i]=-1
        for p in pr:
            if i*p>n: break
            comp[i*p]=True
            if i%p==0: mu[i*p]=0; break
            mu[i*p]=-mu[i]
    return mu
MU = mobius_sieve(4*PREC)

# ---------------- prime zeta with truncation ball (B) ----------------
def log_zeta_1p(eps):
    """Enclosure of log zeta(1+eps), eps>0 arb. Near the pole uses the sandwich
    1/eps < zeta(1+eps) < 1 + 1/eps  (integral comparison, valid 0<eps<1/2),
    hence log zeta(1+eps) in [-log eps, -log eps + eps]."""
    if eps.mid() < EPS_TINY and eps.rad() < EPS_TINY:
        return -eps.log() + arb(0).union(arb(eps))
    return acb.zeta(acb(1) + acb(eps)).log().real

def prime_zeta(j, eps, sf):
    """Enclosure of P(j*(1+eps)); sf = float lower bound of 1+eps."""
    if j == 1:
        tot = log_zeta_1p(eps)
    else:
        tot = acb.zeta(acb(j) + acb(j)*acb(eps)).log().real
    m = 2
    while m*j*sf <= PREC + 30:
        if MU[m]:
            arg = acb(m*j) + acb(m*j)*acb(eps)
            tot += arb(MU[m])/m * acb.zeta(arg).log().real
        m += 1
    err = arb(2)**(2 - m*j*sf)
    return tot + arb(0).union(err.union(-err))

# ---------------- certified GL nodes via interval Newton (D) ----------------
def legendre_pd(n, x):
    p0, p1 = arb(1), x
    for j in range(2, n+1):
        p0, p1 = p1, ((2*j-1)*x*p1 - (j-1)*p0)/j
    return p1, n*(x*p1 - p0)/(x*x - 1)

def gl_certified(n):
    xs, _ = np.polynomial.legendre.leggauss(n)
    nodes, weights = [], []
    for xd in xs:
        x = arb(float(xd))
        for _ in range(5):                      # refine midpoint
            p, dp = legendre_pd(n, x)
            x = arb(x.mid()) - p/dp
            x = arb(x.mid())
        X = x + arb(0).union(arb('1e-30').union(arb('-1e-30')))
        pm, _  = legendre_pd(n, arb(x.mid()))
        _, dPX = legendre_pd(n, X)
        N = arb(x.mid()) - pm/dPX               # interval Newton image
        assert X.contains(N), "interval Newton failed to certify node"
        _, dpN = legendre_pd(n, N)
        w = 2/((1 - N*N)*dpN*dpN)
        nodes.append(N); weights.append(w)
    return nodes, weights

# ---------------- recursion: all P_k at a point ----------------
def all_Pk(eps, sf, kmax):
    Pj=[None]*(kmax+1)
    for j in range(1, kmax+1):
        Pj[j] = prime_zeta(j, eps, sf)
    Pk=[arb(1)]+[arb(0)]*kmax; Pks=[arb(1)]+[arb(0)]*kmax
    for k in range(1, kmax+1):
        acc=arb(0); accs=arb(0)
        for j in range(1, k+1):
            acc  += Pj[j]*Pk[k-j]
            accs += Pj[j]*Pks[k-j] if j%2==1 else -Pj[j]*Pks[k-j]
        Pk[k]=acc/k; Pks[k]=accs/k
    return Pk, Pks

# ---------------- Bernstein-ellipse quadrature bound (C) ----------------
BETA = 2*DELTA/H
RHO  = arb(BETA) + (1 + arb(BETA)**2).sqrt()
EXT  = float((arb(H/2)**2 + arb(DELTA)**2).sqrt().mid())   # semi-major in u units
CQ   = 10 * arb(64)/15 * RHO**(-2*NGL) / (1 - RHO**(-2))   # x10 safety

def panel_gl_error(a, b, kmax):
    """Certified per-k GL error bound for panel [a,b]:
    sup_ellipse |P_k(s(u)) e^-u| <= P_k(sigma_min) * e^-(a-EXT),
    sigma_min = 1 + cos(DELTA) e^-(b+EXT); |Im u| <= DELTA < pi/2 keeps Re s > 1."""
    sig_eps = arb(DELTA).cos() * arb(-(b + EXT)).exp()
    Pk, _ = all_Pk(sig_eps, 1.0, kmax)
    eamp = arb(-(a - EXT)).exp()
    out = []
    for k in range(kmax+1):
        M = (arb(Pk[k].mid()) + arb(Pk[k].rad())) * eamp
        e = CQ * M * arb(H/2)
        out.append(arb(0).union(e.union(-e)))
    return out

# ---------------- tails (E),(F) ----------------
def tail_large_s(k):
    S0 = 1 + arb(-ULO).exp()
    e = arb(2.78)**k * arb(2)**(-k*S0) / (k*arb(2).log())
    return arb(0).union(e.union(-e))

def tail_near_1(k):
    assert UHI >= 2*k + 2
    lf = arb.fac_ui(k) if hasattr(arb,'fac_ui') else arb(1)
    fact = arb(1)
    for i in range(2, k+1): fact *= i
    e = 2 * arb(UHI)**k * arb(-UHI).exp() / fact
    return arb(0).union(e.union(-e))

# ---------------- main ----------------
def run(p0, p1, tag=""):
    t0=time.time()
    nodes, weights = gl_certified(NGL)
    fk=[arb(0)]*(KMAX+1); fks=[arb(0)]*(KMAX+1)
    for pi in range(p0, p1):
        a, b = float(EDGES[pi]), float(EDGES[pi+1])
        ha=(arb(b)-arb(a))/2; mid=(arb(b)+arb(a))/2
        for X, W in zip(nodes, weights):
            u = ha*X + mid; wq = ha*W
            eu = (-u).exp()
            fe = float(eu.mid()); sf = 1.0 + fe*0.999 if fe > 1e-300 else 1.0
            Pk, Pks = all_Pk(eu, sf, KMAX)
            we = wq*eu
            for k in range(1, KMAX+1):
                fk[k]  += we*Pk[k]
                fks[k] += we*Pks[k]
        gerr = panel_gl_error(a, b, KMAX)
        for k in range(1, KMAX+1):
            fk[k] += gerr[k]; fks[k] += gerr[k]
        if (pi+1-p0) % 10 == 0:
            el=time.time()-t0
            print(f"panel {pi+1}/{p1} t={el:.0f}s eta={el/(pi+1-p0)*(p1-pi-1):.0f}s",
                  file=sys.stderr, flush=True)
    if p0 == 0 and p1 == NPANEL:      # complete run: add tails, report
        for k in range(2, KMAX+1):
            fk[k]  += tail_large_s(k) + tail_near_1(k)
            fks[k] += tail_large_s(k) + tail_near_1(k)
            print(k, fk[k].str(30), fks[k].str(30), flush=True)
        mono = all((fk[k+1]-fk[k]) > 0 for k in range(6, KMAX))
        monos = all((fks[k]-fks[k+1]) > 0 for k in range(2, KMAX))
        print(f"# CERTIFIED: f_k strictly increasing on [6,{KMAX}]: {mono}", flush=True)
        print(f"# CERTIFIED: f*_k strictly decreasing on [2,{KMAX}]: {monos}", flush=True)
    else:
        os.makedirs("cchunks", exist_ok=True)
        tmp = f"cchunks/.tmp_c{p0:04d}_{p1:04d}"
        with open(tmp,"w") as f:
            f.write(f"#PARAMS KMAX={KMAX} PREC={PREC} NPANEL={NPANEL} p0={p0} p1={p1}\n")
            for k in range(1, KMAX+1):
                f.write(f"{k} {fk[k].mid().str(170, radius=False)} {arb(fk[k].rad()).str(8, radius=False)} "
                        f"{fks[k].mid().str(170, radius=False)} {arb(fks[k].rad()).str(8, radius=False)}\n")
            f.write("#END\n")
        os.replace(tmp, f"cchunks/c{p0:04d}_{p1:04d}.txt")
    print(f"# done {time.time()-t0:.0f}s", file=sys.stderr)

if __name__ == "__main__":
    if len(sys.argv) > 4:
        run(int(sys.argv[3]), int(sys.argv[4]))
    else:
        run(0, NPANEL)
