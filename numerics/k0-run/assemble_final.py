"""
Final assembly: combine the certified delta-table, the s-uniform S1 bound,
and the S3/U/V constants into the criterion, and find the certified K0.

Run this AFTER delta_parallel.py and s_uniform_parallel.py have produced
their output files (or after extend_head_highprec.py has produced a tighter
S* / S1 bound, if you choose to feed that in instead -- see the NOTE below).

Usage:
    python3 assemble_final.py <delta_pkl> <supF_pkl>
"""
from flint import acb, arb, ctx
import sys, pickle, time
import numpy as np
ctx.prec = 300

def main():
    delta_path = sys.argv[1]
    supF_path = sys.argv[2]
    t0 = time.time()

    D = pickle.load(open(delta_path, 'rb'))
    supF = pickle.load(open(supF_path, 'rb'))
    print(f"delta table: {len(D)} values, range [{min(D)},{max(D)}]")
    print(f"supF: {supF}")

    # Rebuild U, V, rho, supH, cw fresh (these are cheap relative to the
    # delta-table / s-uniform computations, so no separate parallel script
    # was written for them -- see core.py for the underlying engine).
    import core
    from core import wide
    P_BIG = 8_000_000
    eng = core.G2Engine(P=P_BIG, Mterms=210)
    eng5 = core.G2Engine5(P=P_BIG, Mterms=700)
    acc = arb(0); zp = arb(1)
    for m in range(1, eng5.M+1):
        zp *= 3; acc += zp*eng5.PZ[m]/m
    Pa = arb(P_BIG)
    RHO = -3*arb(2)**(-3)*(1-arb(1)/3)**3*(3*eng5.S1+acc+wide(2*(arb(3)/5)**(eng5.M+1)/(1-arb(3)/5))+wide(arb(12)/(2*(1-3/Pa))*(1/(Pa*Pa.log())))).exp()
    R_OUT = arb('4.2'); supH = arb(0)
    for t in range(1024):
        th = 2*arb.pi()*(arb(t)+arb(0).union(arb(1)))/1024
        z, g, _ = core.polar_eval5(eng5, R_OUT, th, want_c=False)
        h = abs(g + acb(RHO)/(z-3)); u = arb(h.mid())+arb(h.rad())
        if u > supH: supH = u
    def absup(x): return arb(abs(x.mid()))+arb(x.rad())
    RHOu = absup(acb(RHO))

    def crude_sup_origin(R):
        aP = arb(0); aQ = arb(0)
        for m in range(1, eng.M+1):
            aP += R**m/m*(arb(eng.PZ[m].mid())+arb(eng.PZ[m].rad()))
            aQ += R**m*(arb(eng.QZ[m].mid())+arb(eng.QZ[m].rad()))
        aQ += arb(eng.QZ[0].mid())+arb(eng.QZ[0].rad())
        aP += (R*R+R)/(2*(1-R/Pa))*(1/(Pa*Pa.log())); aQ += arb('2.21')/Pa/((1-1/Pa)*(1-R/Pa))
        return R*arb(2)**R*(-R*eng.S1).exp()*aP.exp()*(eng.log2+core.GAMMA+(R+1)*aQ)
    SUP25 = crude_sup_origin(arb('2.5'))
    N_C = 256; I0 = 14; vals = []
    for t in range(N_C):
        th = 2*arb.pi()*t/N_C; z = acb(th.cos(), th.sin())
        vals.append((z, eng.G2(z, 1.0)))
    CG = []
    for i in range(I0+1):
        a2 = acb(0)
        for z, g in vals: a2 += g/z**i
        CG.append((a2/N_C).real + wide(SUP25*arb('2.5')**(-(i+N_C))/(1-arb('2.5')**(-N_C))))
    def T_G(i): return RHOu/arb(3)**(i+1) + supH/R_OUT**i
    U = arb(0); V = arb(0)
    for i in range(1, I0+1):
        U += arb(i)*arb(2)**i*CG[i]; V += arb(i)**2*arb(2)**i*CG[i]
    tU = arb(0); tV = arb(0); tS = arb(0)
    for i in range(I0+1, 801):
        w2 = arb(2)**i; tU += arb(i)*w2*T_G(i); tV += arb(i)**2*w2*T_G(i); tS += T_G(i)*w2
    r = arb(2)/3*arb('1.01')
    tU += T_G(801)*arb(801)*arb(2)**801/(1-r); tV += T_G(801)*arb(801)**2*arb(2)**801/(1-r)
    tS += T_G(801)*arb(2)**801/(1-r)
    U = U + wide(tU); V = V + wide(tV)
    Uu = float(absup(acb(U)).mid()); Vu = float(absup(acb(V)).mid())
    tSu = float(tS.mid()+tS.rad())
    L24 = float((arb(2).log()/4).mid())
    cw = [(float(arb((arb(2)**i*CG[i]).mid())), float(arb((arb(2)**i*CG[i]).rad()))) for i in range(I0+1)]
    print(f"U_u={Uu:.6f} V_u={Vu:.6f} tS_u={tSu:.6f}  ({time.time()-t0:.0f}s)")

    def T_G_tail(i):
        if i > 250: return 0.0
        return float(RHOu.mid())/3.0**(i+1) + float(supH.mid())/4.2**i
    A_head = 0.0; B_head = 0.0
    for i in range(1, I0+1):
        ci = supF[i]; A_head += ci*2**(i-1); B_head += i*ci*2**(i-1)
    S_a = 1.5*sum(T_G_tail(i)*2**i for i in range(15, 250))
    AL_S1 = A_head + S_a/2; BE_S1 = A_head - B_head
    print(f"S1 bound: alpha={AL_S1:.6f} beta={BE_S1:.6f}")

    a1l = 0.06562284
    def EA(k): return 2.8552*k*np.log(k+1) + 9.6 + 0.02*k
    def Delta_encl(k):
        lo = 0.0; hi = 0.0
        for i in range(15):
            cm, cr = cw[i]; dlo, dhi = D[k-i]
            c_lo, c_hi = cm-cr, cm+cr
            cands = (c_lo*dlo, c_lo*dhi, c_hi*dlo, c_hi*dhi)
            lo += min(cands); hi += max(cands)
        t = tSu*EA(k)
        return lo-t, hi+t
    def crit_lo(k):
        dk_lo, dk_hi = Delta_encl(k); dk1_lo, dk1_hi = Delta_encl(k+1)
        X_lo = 2*dk_lo - dk1_hi
        dpart_lo = L24*X_lo
        s3_inner_lo = -Vu + (2-2*k)*Uu
        s3_lo = L24*s3_inner_lo
        s1_lo = -(2*(AL_S1*k+BE_S1) + (AL_S1*(k+1)+BE_S1))
        return a1l*(k*k-2*k-1) + s1_lo + s3_lo + dpart_lo - 0.013*3

    k_lo, k_hi = 650, min(9001, max(D)-1)
    bad = [k for k in range(k_lo, k_hi+1) if crit_lo(k) <= 0]
    K0 = max(bad)+1 if bad else k_lo
    print(f"\n=== K0 = {K0} ===")
    allpos = all(crit_lo(k) > 0 for k in range(K0, k_hi+1))
    print(f"Contiguous positivity [{K0},{k_hi}]: {allpos}")
    for k in range(K0-3, K0+4):
        if k in D or k-1 in D:
            print(f"  k={k}: margin={crit_lo(k):.4f}")
    print(f"\nTotal time: {time.time()-t0:.0f}s")

if __name__ == '__main__':
    main()
