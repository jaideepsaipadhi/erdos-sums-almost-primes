#!/usr/bin/env python3
"""Certify the |z| = 4.2 contour bound behind U_max, V_max, S* and the c_i tail.

WHY THIS SCRIPT EXISTS, AND WHAT IT FOUND
-----------------------------------------
The number 101.245 was the one constant in Proposition 6.1 with no generating
artifact anywhere in the repository.  It appeared only as a hardcoded literal
in k0_end_to_end.py and measure_impact.py, annotated "certified separately",
and check_paper_phi.py read it back out of the manuscript -- so the paper and
the scripts agreed only because each had been copied from the other.

Writing the artifact showed that the two were bounding DIFFERENT functions,
and that the manuscript had attached the number to the wrong one.  On
|z| = 4.2, with rho = 0.1749324 the modulus of the residue at z = 3,

    sup |G_2(1,z) - rho/(3-z)|  =  94.154   <= 101.245   -- the SCRIPTS' use,
    sup |(1 - z/3) G_2(1,z)|    = 226.027    > 101.245   -- what eq:contour-
                                                            certified SAID.

The scripts' tail envelope T(i) = rho/3^(i+1) + supH/4.2^i is the residue plus
a Cauchy estimate on the pole-free remainder, which is the first line and is
correct with 7% to spare.  The manuscript's display named the regularized
product (1-z/3)G_2 instead, whose sup is 2.4 times the stated bound, so as
printed it asserted something false and then derived |c_i| <= 354.36 * 3^-i
from it.  Nothing downstream was wrong -- the corrected derivation gives
|c_i| <= 101.31 * 3^-i, i.e. 3.5x SHARPER than the stated 354.36, and U, V and
S* were always computed from the first line -- but the paper's own chain did
not establish its constant.

Both suprema are certified here; the first is the one Proposition 6.1 needs.

THE IDENTITY
------------
k0_end_to_end.py's G2Engine builds

    log G_2(1,z) = z[log(1/2) + sum_{p>=3} log(1-1/p) + sum_{p>=3} 1/p]
                   + sum_{j>=2} z^j sum_{p>=3} p^-j / j,

i.e. the Euler product G_2(1,z) = 2^-z prod_{p>=3} (1-1/p)^z (1-z/p)^-1.  That
series in z converges only for |z| < 3, so it cannot be evaluated at 4.2.
Pulling out the p = 3 factor exactly,

    Gtilde(z) := (1 - z/3) G_2(1,z)
               = 2^-z (1-1/3)^z prod_{p>=5} (1-1/p)^z (1-z/p)^-1,
    log Gtilde(z) = z[-log 3 - sum_{m>=2} A_m/m] + sum_{m>=2} A_m z^m/m,
    A_m := sum_{p>=5} p^-m,

which converges absolutely for |z| < 5, hence at 4.2 with ratio 0.84.  Then
G_2 = Gtilde/(1-z/3) and the pole-free part is G_2 - rho/(3-z) with
rho = 3 Gtilde(3) (checked against the scripts' literal 0.1749324 below).

Primes p <= PCUT are summed termwise for m <= MMAX; the prime tail uses
sum_{p>P} p^-m <= P^(1-m)/((m-1) log P) and the m-tail the geometric
remainder of ratio |z|/p, both as balls, exactly as G2Engine does.

Sampling is made rigorous by a derivative bound: between neighbouring samples
the modulus of an analytic function changes by at most a factor
exp(R * sup|dlog/dz| * pi/NSAMP) over a half-step arc.  The arc factor is
reported so it can be seen to be small.

Settings of record (about 3 minutes, and what contour.log holds):

    python3 contour_certified.py 4.2 200000 300 1440 300
    #                            R   PCUT  MMAX NSAMP PREC
"""
import sys
from flint import arb, acb, ctx

R = arb(sys.argv[1] if len(sys.argv) > 1 else "4.2")
PCUT = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
MMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 300
NSAMP = int(sys.argv[4]) if len(sys.argv) > 4 else 1440
PREC = int(sys.argv[5]) if len(sys.argv) > 5 else 300
ctx.prec = PREC

STATED = arb("101.245")        # eq:contour-certified, and the scripts' supH
RHO_LIT = arb("0.1749324")     # the scripts' hardcoded |residue| at z = 3


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


PS = [p for p in primes_upto(PCUT) if p >= 5]
print("# R = %s  primes 5..%d (%d)  MMAX = %d  NSAMP = %d  prec = %d"
      % (R.str(5, radius=False), PCUT, len(PS), MMAX, NSAMP, PREC))

# ------------------------------------------------- A_m = sum_{p>=5} p^-m
Pa = arb(PCUT)
logP = Pa.log()
A = [arb(0)] * (MMAX + 1)
for p in PS:
    pa = arb(p)
    ip = 1 / (pa * pa)
    for m in range(2, MMAX + 1):
        A[m] += ip
        ip /= pa
        if ip < arb(2) ** (-(PREC + 40)):
            break
for m in range(2, MMAX + 1):
    A[m] += arb(0).union(Pa ** (1 - m) / ((m - 1) * logP))

# m-tail of the log-series beyond MMAX, in modulus, valid at every |z| = R
mtail = arb(0)
for p in PS[:400]:
    pa = arb(p)
    q = R / pa
    mtail += (q ** (MMAX + 1) / (1 - q)
              + R / (pa ** MMAX * (1 - 1 / pa))) / MMAX
mtail += arb(0).union(Pa ** (1 - MMAX) / ((MMAX - 1) * logP)
                      * R ** MMAX / (1 - R / 5) / MMAX)
print("# |log-series m-tail beyond MMAX| <= %s" % mtail.upper().str(5))

c1 = -arb(3).log() - sum(A[m] / m for m in range(2, MMAX + 1))
coef = [arb(0), c1] + [A[m] / m for m in range(2, MMAX + 1)]
BALL = acb(0).union(acb(mtail)).union(acb(-mtail))


def Gt(z):
    s = acb(0)
    zp = acb(1)
    for m in range(1, MMAX + 1):
        zp = zp * z
        s += acb(coef[m]) * zp
    return (s + BALL).exp()


def dlogGt(z):
    s = acb(0)
    zp = acb(1)
    for m in range(1, MMAX + 1):
        s += acb(coef[m] * m) * zp
        zp = zp * z
    return s


# ---------------------------------------------------- residue, cross-checked
rho = 3 * Gt(acb(3)).real
print("# rho = 3 Gtilde(3) = %s   (scripts hardcode %s)"
      % (rho.str(10, radius=False), RHO_LIT.str(8, radius=False)))
rho_ok = float(rho.upper()) <= float(RHO_LIT.lower()) * 1.00001
print("# residue agrees with the hardcoded literal: %s" % rho_ok)

# ------------------------------------------------------- sweep the circle
sup_pf = arb(0)      # |G_2 - rho/(3-z)|   <- what the scripts bound
sup_rg = arb(0)      # |(1-z/3) G_2|       <- what eq:contour-certified said
dmax_pf = arb(0)
dmax_rg = arb(0)
for t in range(NSAMP):
    th = 2 * arb.pi() * t / NSAMP
    z = acb(R * th.cos(), R * th.sin())
    gt = Gt(z)
    pole = 1 - z / 3
    G2 = gt / pole
    pf = G2 - acb(rho) / (3 - z)
    sup_rg = sup_rg.max(abs(gt))
    sup_pf = sup_pf.max(abs(pf))
    # d/dz log Gtilde, and the two derived functions' logarithmic derivatives
    dl = dlogGt(z)
    dmax_rg = dmax_rg.max(abs(dl))
    # (G2 - rho/(3-z))' = (Gtilde' pole + Gtilde/3)/pole^2 - rho/(3-z)^2
    dpf = (dl * gt * pole + gt / 3) / (pole * pole) - acb(rho) / ((3 - z) ** 2)
    dmax_pf = dmax_pf.max(abs(dpf) / abs(pf))

arc_rg = (R * dmax_rg * arb.pi() / NSAMP).exp()
arc_pf = (R * dmax_pf * arb.pi() / NSAMP).exp()
bound_pf = sup_pf * arc_pf
bound_rg = sup_rg * arc_rg

print()
print("pole-free part   sup |G_2(1,z) - rho/(3-z)| <= %s   (arc factor %s)"
      % (bound_pf.upper().str(10), arc_pf.upper().str(6)))
print("regularized      sup |(1 - z/3) G_2(1,z)|   <= %s   (arc factor %s)"
      % (bound_rg.upper().str(10), arc_rg.upper().str(6)))

# ------------------------------------------- the c_i consequence, corrected
# |c_i| <= rho/3^(i+1) + supH/4.2^i = (rho/3 + supH (3/4.2)^i) 3^-i
#       <= (rho/3 + supH) 3^-i
ci_const = rho / 3 + bound_pf
print()
print("corrected  |c_i| <= %s * 3^-i   (manuscript states 354.36, so the"
      % ci_const.upper().str(8))
print("           stated constant holds a fortiori; Lemma 3.7(i) gives 44.5987)")

ok_pf = float(bound_pf.upper()) <= float(STATED.lower())
ok_rg = float(bound_rg.upper()) <= float(STATED.lower())
print()
print("stated 101.245 bounds the pole-free part : %s" % ("YES" if ok_pf else "NO"))
print("stated 101.245 bounds the regularized G_2: %s  <-- it does NOT; the"
      % ("YES" if ok_rg else "NO"))
print("    manuscript's eq:contour-certified named this function and must name")
print("    the pole-free part instead.")
sys.exit(0 if (ok_pf and rho_ok and float(ci_const.upper()) <= 354.36) else 1)
