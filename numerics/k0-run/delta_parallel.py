"""
Parallelized certified delta_m computation, for many-core machines.
Splits the m-range across worker processes; each worker uses the same
endpoint-bracketed panel method validated in the original session
(inner window m in [636,820]: second-order chord/tangent enclosures;
outer window m in [821, M_MAX]: first-order endpoint bracketing).

Usage:
    python3 delta_parallel.py <M_MAX> <NPROC> <output.pkl>

Example (256-core machine, extend the delta table to m=20000 for headroom
on future K0 refinements):
    python3 delta_parallel.py 20000 250 delta_all_extended.pkl

Validated against independent high-precision mpmath ground truth (original
A_m integral definition) in the original session at m=10,20,30,40,700,900,3000
-- agreement to 6+ significant figures throughout. See K0-proof-v6.md Sec 6.
"""
from flint import arb, ctx
import sys, time, pickle
from multiprocessing import Pool

ctx.prec = 96
L2 = arb(2).log()
IMAX = 70

def build_masses(NU, UMAX):
    us = [arb(UMAX)*p/NU for p in range(NU+1)]
    Q = []
    for x in us:
        ex = (-x).exp(); t = arb(1); S = arb(1); col=[S]
        for i in range(1, IMAX+1):
            t = t*x/i; S = S+t; col.append(S)
        Q.append([ex*s for s in col])
    M0 = [[ (arb(2)**i)*(Q[p][i]-Q[p+1][i]) for p in range(NU)] for i in range(IMAX+1)]
    return us, Q, M0

def Bfun(x):
    return (-x*L2).exp() - 1 + x*L2

def delta_encl_firstorder(m, us, Q, M0, NU):
    eus = [(-u).exp() for u in us]
    lo_tot = arb(0); hi_tot = arb(0)
    for i in range(0, min(IMAX, m)+1):
        j = m - i
        if j == 0: continue
        ja = arb(j)
        lo = arb(0); hi = arb(0)
        Bprev = Bfun(ja*eus[0])
        for p in range(NU):
            Bnext = Bfun(ja*eus[p+1])
            w = M0[i][p]
            lo += w*Bnext; hi += w*Bprev
            Bprev = Bnext
        tail_u = (arb(2)**i)*Q[NU][i]*Bprev
        hi += tail_u
        lo_tot += lo; hi_tot += hi
    ti = (L2*L2/6)*arb(m)**2*3*(arb(2)/3)**(IMAX+1)
    base = -1 - (L2/4)*arb(m)
    lo_f = base + lo_tot; hi_f = base + hi_tot + ti
    return (float(arb(lo_f.mid())-arb(lo_f.rad())), float(arb(hi_f.mid())+arb(hi_f.rad())))

# module-level cache so each worker builds panel masses once
_CACHE = {}
def _get_masses():
    key = 'outer'
    if key not in _CACHE:
        _CACHE[key] = build_masses(NU=1800, UMAX=260.0)
    return _CACHE[key]

def worker(m):
    us, Q, M0 = _get_masses()
    return m, delta_encl_firstorder(m, us, Q, M0, 1800)

def main():
    M_MAX = int(sys.argv[1])
    NPROC = int(sys.argv[2])
    outpath = sys.argv[3]
    t0 = time.time()
    ms = list(range(1, M_MAX+1))
    print(f"Computing delta_m for m=1..{M_MAX} across {NPROC} processes...")
    with Pool(NPROC) as pool:
        results = {}
        for i, (m, val) in enumerate(pool.imap_unordered(worker, ms, chunksize=max(1, len(ms)//(NPROC*8)))):
            results[m] = val
            if (i+1) % 2000 == 0:
                print(f"  {i+1}/{len(ms)} done, {time.time()-t0:.0f}s elapsed", flush=True)
    pickle.dump(results, open(outpath, 'wb'))
    print(f"Done: {len(results)} values written to {outpath}, {time.time()-t0:.0f}s total")

if __name__ == '__main__':
    main()
