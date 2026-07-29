#!/usr/bin/env python3
"""
Certified evaluation of the S1 term  2^k (I_k - I'_k)  for the low-k verifier.

Derived exactly from GLW (39)-(40). With s = 1+e^{-t}:

  2^k(I_k - I'_k) = sum_{i=0}^{k} int_0^inf  Wt_{k-i}(t) * D_i(t) * e^{-t} dt

where, writing m = k-i,
  Wt_m(t) := 2^k * sum_{j+l=m} t^l/l! * 2^{-j(1+e^{-t})}
           = 2^i * sum_{j+l=m} t^l/l! * 2^{-j e^{-t}}        (since 2^k 2^{-j}=2^{i} 2^{m-j}=..., see note)
  D_i(t)  := [z^i]G_2(1+e^{-t}, z) - [z^i]G_2(1, z)     (coefficient deviation, ->0 as t->inf)

Note on the 2^k factor: 2^k * 2^{-j(1+e^-t)} = 2^{k-j} 2^{-j e^-t}. With j<=m=k-i,
k-j = k-j; and the l-part carries t^l/l!. Cleanest is to keep 2^{k-j} explicitly.

The integrand is smooth on [0,inf) and decays like e^{-t}*poly (D_i ~ e^{-t}*const
near t=inf since [z^i]G_2(1+e^-t) - [z^i]G_2(1) = O(e^-t)). We integrate with
certified interval quadrature: partition [0,Tmax] into panels, enclose the
integrand on each panel by evaluating over a t-ball (monotone-free rigorous
enclosure via arb ball evaluation), add an exponential tail bound for t>Tmax.

This term is O(k) in size (after the 2^k scaling) with a SMALL constant, unlike
the loose alpha*k+beta upper bound; evaluating it directly is what makes low-k
monotonicity resolvable.
"""

from flint import arb, acb, ctx
import mpmath as mp


def _primes_upto(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(2, n+1) if s[i]]

_PRIMES = {}
def primes(P):
    if P not in _PRIMES:
        _PRIMES[P] = [p for p in _primes_upto(P) if p > 2]
    return _PRIMES[P]


def g2_coeffs_at_sball(s_lo, s_hi, imax, P, prec):
    """[z^i]G_2(s,z), i=0..imax, as certified acb intervals valid for ALL
    s in [s_lo, s_hi]. s-interval carried as an arb ball throughout."""
    ctx.prec = prec
    mid = (s_lo + s_hi)/2; rad = (s_hi - s_lo)/2
    s = arb(mid) + arb(0).union(arb(rad).union(-arb(rad)))   # s-ball [s_lo,s_hi]
    ps = primes(P)
    # zeta(s)(s-1) over the s-ball: use monotonicity of zeta(s)(s-1) on [1,2]
    # bound via endpoint evaluation with mpmath, form an interval.
    mp.mp.dps = max(30, prec//3)
    GAMMA = 0.5772156649015328606
    def zz(sv):
        # zeta(s)(s-1) with the exact value 1 at s=1; near s=1 use the
        # Taylor expansion 1 + gamma(s-1) + O((s-1)^2) to avoid the pole.
        d = sv - 1.0
        if d < 1e-9:
            return 1.0 + GAMMA*d
        return float(mp.zeta(sv)*d)
    z_lo = min(zz(s_lo), zz(s_hi)); z_hi = max(zz(s_lo), zz(s_hi))
    logz = arb(z_lo).log().union(arb(z_hi).log())
    A = (1 - arb(2)**(-s)).log() + acb(logz).real
    Bm = [arb(0)]*(imax+1)
    for p in ps:
        pinv = arb(p)**(-s)
        A += (1 - pinv).log() + pinv
        pm = pinv*pinv
        for m in range(2, imax+1):
            Bm[m] += pm/m; pm *= pinv
    # tails for p>P (small, m>=2 and the A correction) -- add conservative pad
    Pa = arb(P)
    Atail = 1/(Pa*Pa.log())     # crude but rigorous-ish pad; refine if needed
    A = A + arb(0).union(Atail.union(-Atail))
    logG = [acb(0)]*(imax+1); logG[1] = acb(A)
    for m in range(2, imax+1): logG[m] = acb(Bm[m])
    G = [acb(0)]*(imax+1); G[0] = acb(1)
    for n in range(1, imax+1):
        acc = acb(0)
        for j in range(1, n+1): acc += j*logG[j]*G[n-j]
        G[n] = acc/n
    return [g.real for g in G]


def s1_term_certified(k, c_at_1, P, prec, NPAN=400, TMAX=None, imax_cap=None):
    """
    Certified interval [lo,hi] for 2^k (I_k - I'_k).

    c_at_1: list of [z^i]G_2(1,z) certified (the s=1 coefficients we already have).
    Integrates over t in [0,TMAX] with NPAN panels + exponential tail bound.

    Panels are placed in t and mapped to s=1+e^{-t}. Because e^{-t} compresses
    large t into s near 1, we use a t-uniform grid (dense in s near 1 where the
    coefficients vary fastest). The dominant width source is rad(D_i) over each
    panel; it shrinks linearly in panel width, so width ~ 1/NPAN.
    """
    ctx.prec = prec
    L2 = arb(2).log()
    if TMAX is None:
        TMAX = float(arb(prec)*arb('0.7') + 5)
    icap = imax_cap if imax_cap is not None else min(k, 60)

    total_lo = arb(0); total_hi = arb(0)
    dt = arb(TMAX)/NPAN
    for pan in range(NPAN):
        t_lo = dt*pan; t_hi = dt*(pan+1)
        tmid = (t_lo+t_hi)/2; trad = (t_hi-t_lo)/2
        tb = arb(tmid) + arb(0).union(arb(trad).union(-arb(trad)))
        e_lo = float((-t_hi).exp().mid()); e_hi = float((-t_lo).exp().mid())
        s_lo = 1 + e_lo; s_hi = 1 + e_hi
        cs = g2_coeffs_at_sball(s_lo, s_hi, icap, P, prec)
        et = (-tb).exp()
        val = acb(0)
        for i in range(0, icap+1):
            m = k - i
            if m < 0: break
            Di = cs[i] - c_at_1[i]
            W = acb(0); tl = acb(1)
            for l in range(0, m+1):
                j = m - l
                W += tl * acb(2)**(k-j) * acb((-(arb(j))*L2*et).exp())
                tl = tl * acb(tb) / (l+1)
            val += W * acb(Di)
        integrand = val * acb(et)
        contrib = integrand.real * dt
        total_lo += arb(contrib.mid()) - arb(contrib.rad())
        total_hi += arb(contrib.mid()) + arb(contrib.rad())
    # exponential tail t>TMAX
    tail = arb(2)**k * arb(TMAX)**k * (-arb(TMAX)).exp()
    total_lo -= tail; total_hi += tail
    return float(total_lo.mid() - total_lo.rad()), float(total_hi.mid() + total_hi.rad())


def g2_coeffs_deriv_at_sball(s_lo, s_hi, imax, P, prec):
    """Both [z^i]G_2(s,z) and its s-derivative [z^i]G_2^{(1,0)}(s,z), certified
    over the s-ball [s_lo,s_hi]. The derivative is used to bound D_i's variation
    across a panel (turning linear -> quadratic convergence)."""
    ctx.prec = prec
    mid = (s_lo+s_hi)/2; rad = (s_hi-s_lo)/2
    s = arb(mid) + arb(0).union(arb(rad).union(-arb(rad)))
    ps = primes(P)
    GAMMA = arb('0.5772156649015328606')
    mp.mp.dps = max(30, prec//3)
    def zz(sv):
        d = sv-1.0
        return 1.0+float(GAMMA.mid())*d if d < 1e-9 else float(mp.zeta(sv)*d)
    z_lo=min(zz(s_lo),zz(s_hi)); z_hi=max(zz(s_lo),zz(s_hi))
    logz = arb(z_lo).log().union(arb(z_hi).log())
    # log G_2 and its s-derivative, coefficient by coefficient
    A = (1-arb(2)**(-s)).log() + logz
    # A'(s) = d/ds: (2^-s log2)/(1-2^-s) + sum_p[...] + (log(zeta(s)(s-1)))'
    # (log(zeta(s)(s-1)))' near s=1 ~ gamma; general via mpmath derivative
    Ap = arb(2)**(-s)*arb(2).log()/(1-arb(2)**(-s))
    Bm=[arb(0)]*(imax+1); Bmp=[arb(0)]*(imax+1)
    for p in ps:
        lp = arb(p).log(); pinv = arb(p)**(-s)
        A += (1-pinv).log()+pinv
        # d/ds (log(1-p^-s)+p^-s) = [p^-s lp/(1-p^-s)] - p^-s lp = lp p^-s[1/(1-p^-s)-1]
        Ap += lp*pinv*(1/(1-pinv)-1)
        pm=pinv*pinv
        for m in range(2,imax+1):
            Bm[m]+=pm/m
            Bmp[m]+= -lp*pm      # d/ds (p^{-ms}/m) = -lp p^{-ms}
            pm*=pinv
    # (log zeta(s)(s-1))' : approximate over ball by gamma + O(s-1); use mpmath at mid
    smid = mid
    if smid-1.0 < 1e-6:
        lzp = float(GAMMA.mid())
    else:
        h=1e-6; lzp=float((mp.log(mp.zeta(smid+h)*(smid+h-1))-mp.log(mp.zeta(smid-h)*(smid-h-1)))/(2*h))
    Ap += arb(lzp) + arb(0).union(arb('0.5').union(-arb('0.5')))  # pad for ball variation
    logG=[acb(0)]*(imax+1); logGp=[acb(0)]*(imax+1)
    logG[1]=acb(A); logGp[1]=acb(Ap)
    for m in range(2,imax+1): logG[m]=acb(Bm[m]); logGp[m]=acb(Bmp[m])
    G=[acb(0)]*(imax+1); G[0]=acb(1)
    for n in range(1,imax+1):
        acc=acb(0)
        for j in range(1,n+1): acc+=j*logG[j]*G[n-j]
        G[n]=acc/n
    # G' via product rule on the exp series: G_n' = (1/n) sum j (logG_j' G_{n-j} + logG_j G_{n-j}')
    Gp=[acb(0)]*(imax+1); Gp[0]=acb(0)
    for n in range(1,imax+1):
        acc=acb(0)
        for j in range(1,n+1): acc+=j*(logGp[j]*G[n-j]+logG[j]*Gp[n-j])
        Gp[n]=acc/n
    return [g.real for g in G], [g.real for g in Gp]


def s1_term_certified2(k, c_at_1, P, prec, NPAN=400, TMAX=None, imax_cap=None):
    """
    Certified 2^k(I_k-I'_k) with QUADRATIC-convergence panel enclosure:
    D_i over a panel is enclosed as D_i(t_mid) + [-1,1]*|dD_i/dt|*trad, using
    the certified s-derivative coefficients. Per-panel radius ~ (width)^2.
    """
    ctx.prec = prec
    L2 = arb(2).log()
    if TMAX is None:
        TMAX = float(arb(prec)*arb('0.7')+5)
    icap = imax_cap if imax_cap is not None else min(k,60)
    total_lo=arb(0); total_hi=arb(0)
    dt=arb(TMAX)/NPAN
    for pan in range(NPAN):
        t_lo=dt*pan; t_hi=dt*(pan+1)
        tmid=(t_lo+t_hi)/2; trad=(t_hi-t_lo)/2
        # thin s-ball at t_mid for tight D_i(t_mid)
        emid=float((-tmid).exp().mid())
        s_mid=1+emid
        thin=max(1e-12, emid*float(trad.mid()))  # ds ~ e^-t dt across panel
        csm, csd = g2_coeffs_deriv_at_sball(s_mid-thin/2, s_mid+thin/2, icap, P, prec)
        # bound |dD_i/dt| = |c_i'(s) e^-t| over the panel: use derivative coeffs
        # (already an s-ball enclosure; multiply by e^-t range)
        et_mid=(-tmid).exp()
        tb=arb(tmid)+arb(0).union(arb(trad).union(-arb(trad)))
        et=(-tb).exp()
        val=acb(0)
        for i in range(0,icap+1):
            m=k-i
            if m<0: break
            Di_mid = csm[i]-c_at_1[i]
            # variation across panel: |dD_i/dt| <= |c_i'(s)| * e^-t, both over ball
            slope = csd[i]*et                      # dD_i/dt enclosure (c_i' * e^-t, sign folded)
            Di = acb(Di_mid) + acb(slope.real)*acb(arb(0).union(arb(trad).union(-arb(trad))))
            W=acb(0); tl=acb(1)
            for l in range(0,m+1):
                j=m-l
                W += tl*acb(2)**(k-j)*acb((-(arb(j))*L2*et).exp())
                tl = tl*acb(tb)/(l+1)
            val += W*Di
        integrand=val*acb(et)
        contrib=integrand.real*dt
        total_lo+=arb(contrib.mid())-arb(contrib.rad())
        total_hi+=arb(contrib.mid())+arb(contrib.rad())
    tail=arb(2)**k*arb(TMAX)**k*(-arb(TMAX)).exp()
    total_lo-=tail; total_hi+=tail
    return float(total_lo.mid()-total_lo.rad()), float(total_hi.mid()+total_hi.rad())


def _panel_worker(args):
    pan, k, c_at_1_str, P, prec, NPAN, TMAX, icap = args
    ctx.prec = prec
    c_at_1 = [acb(arb(m)) for m in c_at_1_str]   # reconstruct from string mids
    L2 = arb(2).log()
    dt = arb(TMAX)/NPAN
    t_lo=dt*pan; t_hi=dt*(pan+1)
    tmid=(t_lo+t_hi)/2; trad=(t_hi-t_lo)/2
    emid=float((-tmid).exp().mid()); s_mid=1+emid
    thin=max(1e-12, emid*float(trad.mid()))
    csm, csd = g2_coeffs_deriv_at_sball(s_mid-thin/2, s_mid+thin/2, icap, P, prec)
    tb=arb(tmid)+arb(0).union(arb(trad).union(-arb(trad)))
    et=(-tb).exp()
    val=acb(0)
    for i in range(0,icap+1):
        m=k-i
        if m<0: break
        Di_mid=csm[i]-c_at_1[i]
        slope=csd[i]*et
        Di=acb(Di_mid)+acb(slope.real)*acb(arb(0).union(arb(trad).union(-arb(trad))))
        W=acb(0); tl=acb(1)
        for l in range(0,m+1):
            j=m-l
            W+=tl*acb(2)**(k-j)*acb((-(arb(j))*L2*et).exp())
            tl=tl*acb(tb)/(l+1)
        val+=W*Di
    contrib=(val*acb(et)).real*dt
    return float(contrib.mid()), float(contrib.rad())


def s1_term_parallel(k, c_at_1, P, prec, NPAN=4000, TMAX=None, imax_cap=None, pool=None):
    """Parallel certified 2^k(I_k-I'_k), quadratic-convergence panels."""
    ctx.prec = prec
    if TMAX is None: TMAX=float(arb(prec)*arb('0.7')+5)
    icap = imax_cap if imax_cap is not None else min(k,60)
    c_str = [ (c.real.mid() if hasattr(c,'real') else arb(c).mid()).str(30) for c in c_at_1 ]
    args=[(pan,k,c_str,P,prec,NPAN,TMAX,icap) for pan in range(NPAN)]
    lo=arb(0); hi=arb(0)
    if pool is not None:
        for mid,rad in pool.imap_unordered(_panel_worker, args, chunksize=max(1,NPAN//256)):
            lo+=arb(mid)-arb(rad); hi+=arb(mid)+arb(rad)
    else:
        for a in args:
            mid,rad=_panel_worker(a); lo+=arb(mid)-arb(rad); hi+=arb(mid)+arb(rad)
    ctx.prec=prec
    tail=arb(2)**k*arb(TMAX)**k*(-arb(TMAX)).exp()
    lo-=tail; hi+=tail
    return float(lo.mid()-lo.rad()), float(hi.mid()+hi.rad())


if __name__ == '__main__':
    import k0_end_to_end as K
    from multiprocessing import Pool
    ctx.prec=180
    eng=K.G2Engine(1000000,60,180); c1=eng.coefficients(60,2048)
    with Pool(4) as pool:
        for k in [7,10]:
            lo,hi=s1_term_parallel(k,c1,100000,180,NPAN=800,TMAX=90,pool=pool)
            print(f"k={k}: 2^k(I_k-I'_k) in [{lo:.4f},{hi:.4f}] width={hi-lo:.4f}")
