"""Certified evaluation of G2(1,z) and F(z)=G2^{(1,0)}(1,z)=z*G2*c via prime power
sums, enabling large prime cutoffs cheaply.

log G2(z) = -z log2 + z*S1 + sum_{m>=1} z^m PZ[m]/m,   S1 = sum_{p in PS} log(1-1/p)
  (valid |z|<3; PZ[m] = sum_{p in PS} p^-m)
c(z) = log2 + gamma - (z-1)*sum_{m>=0} z^m QZ[m],   QZ[m] = sum log p/((p-1)p^{m+1})

Euler tails (p>P), valid |z|<=R:
  |log G2 tail| <= (R^2+R)/(2(1-R/P)) * 1/(P log P)          [note (3.2a)]
  |c tail|      <= (R+1) * 1.1*(log P + 1)/P / (1 - R/P)      [sum log p/p^2 tail]
"""
from flint import acb, arb, ctx
import math

GAMMA = arb('0.577215664901532860606512090082402431042159335939923598805767')

def primes_upto(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2, int(n**0.5)+1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n+1) if s[i]]   # p>2 only

class G2Engine:
    def __init__(self, P, Mterms):
        self.P = P; self.M = Mterms
        ps = primes_upto(P)
        self.S1 = arb(0)
        pz = [arb(0)]*(Mterms+1)
        qz = [arb(0)]*(Mterms+1)
        cut = arb(2)**(-(ctx.prec + 40))
        for p in ps:
            pa = arb(p)
            self.S1 += (1 - 1/pa).log()
            lp = pa.log()
            ipow = 1/pa
            q0 = lp/(pa-1)
            for m in range(1, Mterms+1):
                pz[m] += ipow
                qz[m-1] += q0*ipow
                ipow /= pa
                if ipow < cut:
                    break
        # dropped terms: each < cut per prime, <= len(ps) * cut in total per index
        npc = arb(len(ps))*cut
        def w(m, base):
            pm = min(2*arb(base)**(-m), npc) if m >= 1 else npc
            return arb(0).union(pm.union(-pm))
        self.PZ = [pz[m] + w(m,3) for m in range(Mterms+1)]
        self.QZ = [qz[m] + w(m+1,3) for m in range(Mterms+1)]
        self.log2 = arb(2).log()

    def _series_ball(self, z, R):
        """log G2 series + truncation ball for |z|<=R<3 (needs (R/3)^M tiny)."""
        acc = acb(0); zp = acb(1)
        for m in range(1, self.M+1):
            zp *= z
            acc += zp*self.PZ[m]/m
        # series truncation: sum_{m>M} R^m * PZ_true[m]/m <= sum (R/3)^m * (#eff)
        # PZ[m] <= 3^-m * (1 + (3/5)^m + ...) <= 2*3^-m for m>=2
        t = 2*(arb(R)/3)**(self.M+1)/(1-arb(R)/3)
        return acc + acb(arb(0).union(t.union(-t)), arb(0).union(t.union(-t)))

    def G2(self, z, R):
        """Certified G2(1,z) for |z|<=R (R<3, R<P). z may be a ball covering an arc."""
        lg = -z*self.log2 + z*self.S1 + self._series_ball(z, R)
        # Euler tail on log
        Ra = arb(R); Pa = arb(self.P)
        t1 = (Ra*Ra+Ra)/(2*(1-Ra/Pa)) * (1/(Pa*Pa.log()))
        lg += acb(arb(0).union(t1.union(-t1)), arb(0).union(t1.union(-t1)))
        return lg.exp()

    def c(self, z, R):
        acc = acb(0); zp = acb(1)
        for m in range(0, self.M+1):
            acc += zp*self.QZ[m]
            zp *= z
        # series truncation: QZ_true[m] ~ log3/2 * 3^{-m-1}*(1+...) <= 1.2*log(3)/2*3^-m-1... bound 3^-m
        t = (arb(R)/3)**(self.M+1)/(1-arb(R)/3)
        acc += acb(arb(0).union(t.union(-t)), arb(0).union(t.union(-t)))
        # Euler tail: sum_{p>P} log p/((p-1)(p-z)), |.| <= 1.1(log P+1)/P /(1-R/P) *... per-prime
        Ra = arb(R); Pa = arb(self.P)
        t2 = arb('1.2')*(Pa.log()+1)/Pa/(1-Ra/Pa)
        tail = acb(arb(0).union(t2.union(-t2)), arb(0).union(t2.union(-t2)))
        return acb(self.log2 + GAMMA) - (z-1)*(acc + tail)

    def F(self, z, R):
        """G2^{(1,0)}(1,z) = z*G2(1,z)*c(1,z)."""
        return z*self.G2(z, R)*self.c(z, R)

def wide(r):
    """symmetric real ball [-r, r]"""
    return arb(0).union(r.union(-r))

class G2Engine5:
    """Same, but p>=5 only; the p=3 factors are handled exactly by the caller.
    Valid for |z| < 5. G2(1,z) = 2^-z (1-1/3)^z (1-z/3)^-1 * exp(z*S1 + series).
    c(1,z) = log2+gamma - (z-1)[ log3/(2(3-z)) + sum_m z^m QZ[m] ]."""
    def __init__(self, P, Mterms):
        self.P = P; self.M = Mterms
        ps = [p for p in primes_upto(P) if p >= 5]
        self.nps = len(ps)
        cut = arb(2)**(-(ctx.prec + 40))
        self.S1 = arb(0)
        pz = [arb(0)]*(Mterms+1); qz = [arb(0)]*(Mterms+1)
        for p in ps:
            pa = arb(p)
            self.S1 += (1 - 1/pa).log()
            ipow = 1/pa
            q0 = pa.log()/(pa-1)
            for m in range(1, Mterms+1):
                pz[m] += ipow
                qz[m-1] += q0*ipow
                ipow /= pa
                if ipow < cut:
                    break
        npc = arb(len(ps))*cut
        def w(m, base):
            pm = min(2*arb(base)**(-m), npc) if m >= 1 else npc
            return arb(0).union(pm.union(-pm))
        self.PZ = [pz[m] + w(m,5) for m in range(Mterms+1)]
        self.QZ = [qz[m] + w(m+1,5) for m in range(Mterms+1)]
        self.log2 = arb(2).log()
        self.third = arb(1)/3

    def G2(self, z, R):
        acc = acb(0); zp = acb(1)
        for m in range(1, self.M+1):
            zp *= z
            acc += zp*self.PZ[m]/m
        t = 2*(arb(R)/5)**(self.M+1)/(1-arb(R)/5)
        acc += acb(wide(t), wide(t))
        Ra = arb(R); Pa = arb(self.P)
        t1 = (Ra*Ra+Ra)/(2*(1-Ra/Pa)) * (1/(Pa*Pa.log()))
        lg = -z*self.log2 + z*self.S1 + acc + acb(wide(t1), wide(t1))
        pole3 = (1-self.third)**z * (1-z*self.third)**(-1)
        return lg.exp()*pole3

    def c(self, z, R):
        acc = acb(0); zp = acb(1)
        for m in range(0, self.M+1):
            acc += zp*self.QZ[m]
            zp *= z
        t = (arb(R)/5)**(self.M+1)/(1-arb(R)/5)
        acc += acb(wide(t), wide(t))
        Ra = arb(R); Pa = arb(self.P)
        # theta(x) <= 1.017x  =>  sum_{p>P} log p/p^2 <= 2.04/P; /(1-1/P)(1-R/P)
        t2 = arb('2.04')/Pa/((1-1/Pa)*(1-Ra/Pa))
        p3 = arb(3).log()/(2*(3-z))
        return acb(self.log2 + GAMMA) - (z-1)*(p3 + acc + acb(wide(t2), wide(t2)))

    def F(self, z, R):
        return z*self.G2(z, R)*self.c(z, R)

def polar_eval5(eng5, R, th, want_c=True):
    """Certified G2 (and c) at z = R*e^{i th}, R an exact-ish arb, th a ball.
    Series powers computed in polar form: no rectangular rotation loss."""
    z = acb(R*th.cos(), R*th.sin())
    accG = acb(0); accC = acb(0)
    Rm = arb(1); ang = arb(0)
    for m in range(0, eng5.M+1):
        if m >= 1:
            Rm *= R; ang += th
            w = acb(ang.cos(), ang.sin())
            zp = Rm*w
            accG += zp*eng5.PZ[m]/m
            if want_c:
                accC += zp*eng5.QZ[m]
        elif want_c:
            accC += eng5.QZ[0]
    tG = 2*(R/5)**(eng5.M+1)/(1-R/5)
    accG += acb(wide(tG), wide(tG))
    Pa = arb(eng5.P)
    t1 = (R*R+R)/(2*(1-R/Pa)) * (1/(Pa*Pa.log()))
    lg = -z*eng5.log2 + z*eng5.S1 + accG + acb(wide(t1), wide(t1))
    G2v = lg.exp() * (1-eng5.third)**z * (1-z*eng5.third)**(-1)
    if not want_c:
        return z, G2v, None
    tC = (R/5)**(eng5.M+1)/(1-R/5)
    accC += acb(wide(tC), wide(tC))
    t2 = arb('2.04')/Pa/((1-1/Pa)*(1-R/Pa))
    p3 = arb(3).log()/(2*(3-z))
    cv = acb(eng5.log2 + GAMMA) - (z-1)*(p3 + accC + acb(wide(t2), wide(t2)))
    return z, G2v, cv

def crude_sup_F_circle3(eng5, r):
    """Rigorous bound on sup_{|z-3|=r} |F|, r<2, via factorwise product bounds.
    |G2| <= 2^{-Rmin} * (3/d3) * (5/d5) * exp(sum_{p>=7} -log(1-Zm/p)) * tails
    with Zm = 3+r (max |z|), d3 = r, d5 = 5-3-r = 2-r, dp = p-(3+r)."""
    Zm = arb(3)+r
    # sum_{p>=7} -log(1-Zm/p) = sum_m Zm^m/m * (PZ5[m]-5^-m), + Euler tail
    acc = arb(0)
    for m in range(1, eng5.M+1):
        pz7 = eng5.PZ[m] - arb(5)**(-m)
        acc += Zm**m/m * (arb(pz7.mid())+arb(pz7.rad()))
        if Zm**m * 2*arb(7)**(-m) < arb(2)**(-80):
            break
    Pa = arb(eng5.P)
    acc += (Zm*Zm+Zm)/(2*(1-Zm/Pa)) * (1/(Pa*Pa.log()))
    g2 = arb(2)**(-(3-r)) * (3/r) * (5/(2-r)) * acc.exp()
    # |c| <= log2+gamma + (Zm+1)*( log3/(2 r) + log5/(4(2-r)) + sum_{p>=7} log p/((p-1)(p-Zm)) )
    accc = arb(0)
    for m in range(0, eng5.M+1):
        q7 = eng5.QZ[m] - arb(5).log()/(4*arb(5)**(m+1))
        accc += Zm**m * (arb(q7.mid())+arb(q7.rad()))
        if Zm**m * arb(7).log()*arb(7)**(-m-1) < arb(2)**(-80):
            break
    accc += arb('2.04')/Pa/((1-1/Pa)*(1-Zm/Pa))
    cb = eng5.log2 + GAMMA + (Zm+1)*(arb(3).log()/(2*r) + arb(5).log()/(4*(2-r)) + accc)
    return Zm * g2 * cb
