from flint import acb, arb, ctx
import time
ctx.prec = 300
import k0_end_to_end as K

def absup(x): return arb(abs(x.mid())) + arb(x.rad())

def build_consts(P, prec, shrink_radii=False):
    eng = K.G2Engine(P, 210, prec)
    CG = eng.coefficients(14, 4096)
    imax = 14
    if shrink_radii:
        CG = [acb(arb(c.real.mid(), 1e-7), arb(c.imag.mid(), 1e-7)) for c in CG]
    U = arb(0); V = arb(0); Sstar = arb(0)
    for i in range(imax+1):
        w = arb(2)**i
        U += arb(i)*w*CG[i]; V += arb(i)**2*w*CG[i]; Sstar += w*absup(CG[i])
    rho_mag = arb('0.1749324'); supH = arb('101.245'); R = arb('4.2')
    def T(i): return rho_mag/arb(3)**(i+1) + supH/R**i
    tU=arb(0); tV=arb(0); tS=arb(0)
    for i in range(imax+1, 801):
        w=arb(2)**i; tU+=arb(i)*w*T(i); tV+=arb(i)**2*w*T(i); tS+=w*T(i)
    ratio=arb(2)/3*arb('1.01')
    tU+=T(801)*arb(801)*arb(2)**801/(1-ratio); tV+=T(801)*arb(801)**2*arb(2)**801/(1-ratio)
    tS+=T(801)*arb(2)**801/(1-ratio)
    U=U+arb(0).union(tU.union(-tU)); V=V+arb(0).union(tV.union(-tV)); Sstar=Sstar+tS
    cw=[(float((arb(2)**i*CG[i]).real.mid()), float((arb(2)**i*CG[i]).real.rad())) for i in range(imax+1)]
    return dict(U=U,V=V,Sstar=Sstar,cw=cw,tS=float(tS.mid()+tS.rad()))

# realistic supF from your last good run
supF = [0.0, 1.6792360, 1.7005502, 0.9364731, 0.3734471, 0.1141119,
        0.0345, 0.0098, 0.0028, 0.00082, 0.00025, 7.5e-5, 2.3e-5, 8e-6, 3e-6]

import sys
NPROC = int(sys.argv[1]) if len(sys.argv) > 1 else 4
print(f"Building delta table to m=9016 across {NPROC} procs (slow part)...")
t0 = time.time()
D = K.build_delta_table(9016, NPROC)
print(f"  done {time.time()-t0:.0f}s\n")

for label, shrink in [("current radii (~3.28e-4)", False), ("shrunk radii (~1e-7)", True)]:
    consts = build_consts(8000000, 300, shrink_radii=shrink)
    K0, crit = K.k0_tight(consts, supF, D, verbose=False)
    print(f"{label:28s}: K0_TIGHT = {K0}   margin@K0={crit(K0):.2f}  margin@K0-1={crit(K0-1):.2f}")
    print(f"    U_u={float(absup(consts['U'])):.6f}  V_u={float(absup(consts['V'])):.6f}  S*={float(consts['Sstar'].mid()):.5f}\n")

print("If the two K0 values are within a few of each other, the noise floor")
print("is NOT worth chasing. If they differ by tens, it is.")
