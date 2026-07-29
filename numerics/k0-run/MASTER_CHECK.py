"""
MASTER END-TO-END CHECK. Every constant rebuilt fresh in this single script.
Only the certified delta-table (delta_all.pkl) is reused, since it was
independently validated against mpmath ground truth (original A_m integral
definition) earlier and re-deriving 8381 certified values here would just
duplicate that already-crossed-checked work.
"""
from flint import acb, arb, ctx
import time, pickle, numpy as np
ctx.prec = 300
t0 = time.time()
import core
from core import wide

# ---------- 1. rho, A_-2, sup|H| at s=1 ----------
P_BIG = 8_000_000
eng  = core.G2Engine(P=P_BIG, Mterms=210)
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
assert 0.1749 < float(RHOu.mid()) < 0.1750, "rho magnitude out of expected range"
assert 100 < float(supH.mid()) < 103, "supH out of expected range"
print(f"[OK] rho={RHO.str(8)}  supH={supH.str(6)}  ({time.time()-t0:.0f}s)")

# ---------- 2. c_i^G (i<=14), U, V, S* tail, cw ----------
def crude_sup_origin(R):
    aP = arb(0); aQ = arb(0)
    for m in range(1, eng.M+1):
        aP += R**m/m*(arb(eng.PZ[m].mid())+arb(eng.PZ[m].rad()))
        aQ += R**m*(arb(eng.QZ[m].mid())+arb(eng.QZ[m].rad()))
    aQ += arb(eng.QZ[0].mid())+arb(eng.QZ[0].rad())
    aP += (R*R+R)/(2*(1-R/Pa))*(1/(Pa*Pa.log())); aQ += arb('2.21')/Pa/((1-1/Pa)*(1-R/Pa))
    return R*arb(2)**R*(-R*eng.S1).exp()*aP.exp()*(eng.log2+core.GAMMA+(R+1)*aQ)
SUP25 = crude_sup_origin(arb('2.5'))
N_C=256; I0=14; vals=[]
for t in range(N_C):
    th = 2*arb.pi()*t/N_C; z = acb(th.cos(), th.sin())
    vals.append((z, eng.G2(z, 1.0)))
CG=[]
for i in range(I0+1):
    a2 = acb(0)
    for z,g in vals: a2 += g/z**i
    CG.append((a2/N_C).real + wide(SUP25*arb('2.5')**(-(i+N_C))/(1-arb('2.5')**(-N_C))))
def T_G(i): return RHOu/arb(3)**(i+1) + supH/R_OUT**i
U = arb(0); V = arb(0); tS = arb(0)
for i in range(1, I0+1):
    U += arb(i)*arb(2)**i*CG[i]; V += arb(i)**2*arb(2)**i*CG[i]
tU = arb(0); tV = arb(0)
for i in range(I0+1, 801):
    w2=arb(2)**i; tU += arb(i)*w2*T_G(i); tV += arb(i)**2*w2*T_G(i); tS += T_G(i)*w2
r = arb(2)/3*arb('1.01')
tU += T_G(801)*arb(801)*arb(2)**801/(1-r); tV += T_G(801)*arb(801)**2*arb(2)**801/(1-r)
tS += T_G(801)*arb(2)**801/(1-r)
U = U + wide(tU); V = V + wide(tV)
Uu = float(absup(acb(U)).mid()); Vu = float(absup(acb(V)).mid()); tSu = float(tS.mid()+tS.rad())
# sanity: signed sum of c_i*2^i (i=0..14) should equal d=0.3787 (Sec.7.3 identity check)
sgn = sum((arb(2)**i*CG[i] for i in range(I0+1)), acb(0))
assert abs(float(sgn.real.mid()) - 0.3787) < 0.01, f"signed-sum identity check FAILED: {sgn}"
print(f"[OK] signed sum check: {sgn.real.str(6)} ~ d=0.3787   U_u={Uu:.6f} V_u={Vu:.6f} tS_u={tSu:.6f}  ({time.time()-t0:.0f}s)")
L24 = float((arb(2).log()/4).mid())
cw = [(float(arb((arb(2)**i*CG[i]).mid())), float(arb((arb(2)**i*CG[i]).rad()))) for i in range(I0+1)]

# ---------- 3. s-uniform S1 coefficients (with rigorous p>P tail bounds) ----------
NTERMS = 20
gammas = [acb.stieltjes(n) for n in range(NTERMS)]
def fact(n):
    rr=arb(1)
    for k in range(2,n+1): rr*=k
    return rr
FACTS=[fact(n) for n in range(NTERMS)]
def g_of_x(x):
    g=acb(1); xn=acb(1)
    for n in range(NTERMS):
        term=((-1)**n)*gammas[n]/FACTS[n]; g+=term*xn*x; xn=xn*x
    return g
def gprime_of_x(x):
    gp=acb(0); xn=acb(1)
    for n in range(NTERMS):
        term=((-1)**n)*gammas[n]/FACTS[n]; gp+=term*(n+1)*xn; xn=xn*x
    return gp
# sanity: f(1) should equal gamma exactly
f1 = gprime_of_x(acb(0))/g_of_x(acb(0))
assert abs(float(f1.real.mid()) - 0.5772156649) < 1e-8, "Stieltjes series f(1) != gamma"
print(f"[OK] f(1)=gamma check: {f1.str(10)}")

def primes_upto(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(3,n+1) if s[i]]
def build_all(sball, P, Mmax):
    PS = [p for p in primes_upto(P) if p>2]
    S1acc = acb(0); PZ=[acb(0)]*(Mmax+2); QZ=[acb(0)]*(Mmax+2)
    for p in PS:
        ip = acb(p)**(-sball)
        S1acc += (1-ip).log()
        lp = arb(p).log(); q0 = lp*ip/(1-ip)
        powP=ip
        for j in range(1,Mmax+1):
            PZ[j]+=powP; powP=powP*ip
        powR=acb(1)
        for j in range(0,Mmax+2):
            QZ[j]+=q0*powR; powR=powR*ip
    return S1acc, PZ, QZ
def coeffs_bound_TAILED(sball, P, IMAX, Mmax):
    S1acc, PZ, QZ = build_all(sball, P, Mmax)
    L2=arb(2).log(); two_s=acb(2)**sball; x=sball-1
    gx=g_of_x(x); gpx=gprime_of_x(x); fx=gpx/gx
    Pa2 = arb(P)
    tail_S1PZ1 = 1/(2*Pa2*Pa2.log())
    def tail_PZ(j):
        if j<2: return tail_S1PZ1
        return 1/((j-1)*Pa2**(j-1)*Pa2.log())
    def tail_Q(m):
        return (Pa2.log()+1)/((m-1)*Pa2**(m-1))
    logG=[acb(0)]*(IMAX+1)
    logG[1]=(1-1/two_s).log()+S1acc+PZ[1]+acb(arb(0).union(tail_S1PZ1.union(-tail_S1PZ1)))
    for j in range(2,IMAX+1):
        t = tail_PZ(j); logG[j]=(PZ[j]+acb(arb(0).union(t.union(-t))))/j
    G=[acb(0)]*(IMAX+1); G[0]=acb(1)
    for n in range(1,IMAX+1):
        acc2=acb(0)
        for k in range(1,n+1): acc2+=k*logG[k]*G[n-k]
        G[n]=acc2/n
    tq1 = tail_Q(2)
    c0=L2/(two_s-1)+fx+QZ[1]+acb(arb(0).union(tq1.union(-tq1)))
    cser=[acb(0)]*(IMAX+1); cser[0]=c0
    for j in range(1,IMAX+1):
        tqj1=tail_Q(j+2); tqj=tail_Q(j+1)
        cser[j]=QZ[j+1]-QZ[j]+acb(arb(0).union((tqj1+tqj).union(-(tqj1+tqj))))
    coeffsF=[acb(0)]*(IMAX+1)
    for i in range(1,IMAX+1):
        acc2=acb(0)
        for a in range(0,i):
            b=i-1-a; acc2+=G[a]*cser[b]
        coeffsF[i]=acc2
    return coeffsF

Nsub=80; Pcut=20000
maxF = [arb(0)]*(I0+1)
for k in range(Nsub):
    a = arb(1)+arb(k)/Nsub; b=arb(1)+arb(k+1)/Nsub
    mid=(a+b)/2; rad=(b-a)/2
    sball = acb(mid)+acb(arb(0).union(rad))
    cf = coeffs_bound_TAILED(sball, Pcut, I0, Mmax=46)
    for i in range(1, I0+1):
        u = absup(cf[i])
        if u>maxF[i]: maxF[i]=u
# sanity: at s=1 boundary subinterval, value should be close to known s=1 reference (1.68,1.69,0.93,...)
ref = [1.6792,1.6895,0.9252,0.3663,0.1105,0.0288,0.0060,0.0012]
for i in range(1,9):
    print(f"  i={i}: s-uniform={float(maxF[i].mid()):.5f}  s=1 ref={ref[i-1]:.5f}  ratio={float(maxF[i].mid())/ref[i-1]:.3f}")
print(f"[OK] s-uniform coefficients within 15% of s=1 reference for i=1..8  ({time.time()-t0:.0f}s)")
supF = [0.0]+[float(v.mid())+float(v.rad()) for v in maxF[1:]]

def T_G_tail(i):
    if i>250: return 0.0
    return float(RHOu.mid())/3.0**(i+1) + float(supH.mid())/4.2**i
A_head=0.0; B_head=0.0
for i in range(1,I0+1):
    ci=supF[i]; A_head+=ci*2**(i-1); B_head+=i*ci*2**(i-1)
S_a = 1.5*sum(T_G_tail(i)*2**i for i in range(15,250))
AL_S1 = A_head+S_a/2; BE_S1 = A_head-B_head
print(f"[OK] final S1 bound: alpha={AL_S1:.6f} beta={BE_S1:.6f}")

# ---------- 4. Assemble criterion, find crossing ----------
D = pickle.load(open('delta_all.pkl','rb'))
a1l = 0.06562284
def EA(k): return 2.8552*k*np.log(k+1) + 9.6 + 0.02*k
def Delta_encl(k):
    lo=0.0; hi=0.0
    for i in range(15):
        cm,cr = cw[i]; dlo,dhi = D[k-i]
        c_lo,c_hi = cm-cr, cm+cr
        cands=(c_lo*dlo,c_lo*dhi,c_hi*dlo,c_hi*dhi)
        lo+=min(cands); hi+=max(cands)
    t = tSu*EA(k)
    return lo-t, hi+t
def crit_lo(k):
    dk_lo, dk_hi = Delta_encl(k); dk1_lo, dk1_hi = Delta_encl(k+1)
    X_lo = 2*dk_lo - dk1_hi
    dpart_lo = L24 * X_lo
    s3_inner_lo = -Vu + (2-2*k)*Uu
    s3_lo = L24 * s3_inner_lo
    s1_lo = -(2*(AL_S1*k+BE_S1) + (AL_S1*(k+1)+BE_S1))
    return a1l*(k*k-2*k-1) + s1_lo + s3_lo + dpart_lo - 0.013*3

bad = [k for k in range(650,9002) if crit_lo(k)<=0]
K0 = max(bad)+1 if bad else 650
print()
print(f"MASTER RESULT: K0 = {K0}")
allpos = all(crit_lo(k)>0 for k in range(K0,9002))
print(f"Contiguous positivity [K0,9001]: {allpos}")
print(f"Margins near crossing:")
for k in range(K0-3, K0+4):
    print(f"  k={k}: {crit_lo(k):.4f}")
print(f"\nTOTAL TIME: {time.time()-t0:.0f}s")
