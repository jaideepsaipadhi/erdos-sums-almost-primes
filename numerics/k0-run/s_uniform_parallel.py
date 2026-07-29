"""
Parallelized certified evaluation of sup_{s in [1,2]} |[z^i]G_2^{(1,0)}(s,z)|
for i=1..IMAX, via direct series recursion with s as a certified interval
(NOT Cauchy contour estimates -- those lose the cancellation that makes these
values small; see K0-proof-v6.md Sec 4 and Sec 8 item 2 for why).

Validated in the original session against known s=1 reference values to
4+ decimal places, and cross-checked for stability under P: 20000 -> 35000
(see Sec 8 item 4 for the tail-bound bug that was found and fixed along the
way -- use the tail-bound version below, not a naive truncation).

Usage:
    python3 s_uniform_parallel.py <NSUB> <P_CUTOFF> <NPROC> <output.pkl>

Example (256 cores -- go much finer and larger than the original session's
NSUB=80, P=20000 to shrink the certified enclosures further):
    python3 s_uniform_parallel.py 2000 2000000 250 supF_highres.pkl
"""
from flint import acb, arb, ctx
import sys, time, pickle
from multiprocessing import Pool

ctx.prec = 200
NTERMS = 20

def get_gammas():
    return [acb.stieltjes(n) for n in range(NTERMS)]

def fact(n):
    r = arb(1)
    for k in range(2, n+1): r *= k
    return r

FACTS = [fact(n) for n in range(NTERMS)]

def g_of_x(x, gammas):
    g = acb(1); xn = acb(1)
    for n in range(NTERMS):
        term = ((-1)**n)*gammas[n]/FACTS[n]
        g += term*xn*x; xn = xn*x
    return g

def gprime_of_x(x, gammas):
    gp = acb(0); xn = acb(1)
    for n in range(NTERMS):
        term = ((-1)**n)*gammas[n]/FACTS[n]
        gp += term*(n+1)*xn; xn = xn*x
    return gp

def primes_upto(n):
    s = bytearray([1])*(n+1); s[0] = s[1] = 0
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n+1) if s[i]]

_PRIME_CACHE = {}
def get_primes(P):
    if P not in _PRIME_CACHE:
        _PRIME_CACHE[P] = [p for p in primes_upto(P) if p > 2]
    return _PRIME_CACHE[P]

def build_all(sball, P, Mmax):
    PS = get_primes(P)
    S1acc = acb(0)
    PZ = [acb(0)]*(Mmax+2); QZ = [acb(0)]*(Mmax+2)
    for p in PS:
        ip = acb(p)**(-sball)
        S1acc += (1-ip).log()
        lp = arb(p).log(); q0 = lp*ip/(1-ip)
        powP = ip
        for j in range(1, Mmax+1):
            PZ[j] += powP; powP = powP*ip
        powR = acb(1)
        for j in range(0, Mmax+2):
            QZ[j] += q0*powR; powR = powR*ip
    return S1acc, PZ, QZ

def absup(v): return arb(abs(v.mid())) + arb(v.rad())

def coeffs_bound_TAILED(sball, P, IMAX, Mmax, gammas):
    S1acc, PZ, QZ = build_all(sball, P, Mmax)
    L2 = arb(2).log(); two_s = acb(2)**sball; x = sball - 1
    gx = g_of_x(x, gammas); gpx = gprime_of_x(x, gammas); fx = gpx/gx
    Pa = arb(P)
    tail_S1PZ1 = 1/(2*Pa*Pa.log())
    def tail_PZ(j):
        if j < 2: return tail_S1PZ1
        return 1/((j-1)*Pa**(j-1)*Pa.log())
    def tail_Q(m):
        return (Pa.log()+1)/((m-1)*Pa**(m-1))
    logG = [acb(0)]*(IMAX+1)
    logG[1] = (1-1/two_s).log() + S1acc + PZ[1] + acb(arb(0).union(tail_S1PZ1.union(-tail_S1PZ1)))
    for j in range(2, IMAX+1):
        t = tail_PZ(j)
        logG[j] = (PZ[j] + acb(arb(0).union(t.union(-t))))/j
    G = [acb(0)]*(IMAX+1); G[0] = acb(1)
    for n in range(1, IMAX+1):
        acc = acb(0)
        for k in range(1, n+1): acc += k*logG[k]*G[n-k]
        G[n] = acc/n
    tq1 = tail_Q(2)
    c0 = L2/(two_s-1) + fx + QZ[1] + acb(arb(0).union(tq1.union(-tq1)))
    cser = [acb(0)]*(IMAX+1); cser[0] = c0
    for j in range(1, IMAX+1):
        tqj1 = tail_Q(j+2); tqj = tail_Q(j+1)
        cser[j] = QZ[j+1] - QZ[j] + acb(arb(0).union((tqj1+tqj).union(-(tqj1+tqj))))
    coeffsF = [acb(0)]*(IMAX+1)
    for i in range(1, IMAX+1):
        acc = acb(0)
        for a in range(0, i):
            b = i-1-a; acc += G[a]*cser[b]
        coeffsF[i] = acc
    return [absup(c) for c in coeffsF]

_GAMMAS_CACHE = None
def worker(args):
    global _GAMMAS_CACHE
    if _GAMMAS_CACHE is None:
        _GAMMAS_CACHE = get_gammas()
    k, NSUB, P, IMAX, Mmax = args
    a = arb(1) + arb(k)/NSUB
    b = arb(1) + arb(k+1)/NSUB
    mid = (a+b)/2; rad = (b-a)/2
    sball = acb(mid) + acb(arb(0).union(rad))
    bounds = coeffs_bound_TAILED(sball, P, IMAX, Mmax, _GAMMAS_CACHE)
    return [float(v.mid())+float(v.rad()) for v in bounds]

def main():
    NSUB = int(sys.argv[1])
    P = int(sys.argv[2])
    NPROC = int(sys.argv[3])
    outpath = sys.argv[4]
    IMAX = 14
    Mmax = 46
    t0 = time.time()
    print(f"NSUB={NSUB} P={P} NPROC={NPROC}  -- computing s-uniform coefficient bounds...")
    args = [(k, NSUB, P, IMAX, Mmax) for k in range(NSUB)]
    maxF = [0.0]*(IMAX+1)
    with Pool(NPROC) as pool:
        for i, bounds in enumerate(pool.imap_unordered(worker, args, chunksize=max(1,NSUB//(NPROC*4)))):
            for j in range(1, IMAX+1):
                if bounds[j] > maxF[j]: maxF[j] = bounds[j]
            if (i+1) % max(1,NSUB//20) == 0:
                print(f"  {i+1}/{NSUB} subintervals done, {time.time()-t0:.0f}s", flush=True)
    print("Certified sup_{s in [1,2]} |c_i^F(s)|:")
    for i in range(1, IMAX+1):
        print(f"  i={i}: {maxF[i]:.10g}")
    pickle.dump(maxF, open(outpath, 'wb'))
    print(f"Done, {time.time()-t0:.0f}s total. Written to {outpath}")

if __name__ == '__main__':
    main()
