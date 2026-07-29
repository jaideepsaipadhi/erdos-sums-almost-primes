"""
Attempt to extend the certified coefficient head (currently i0=14, limited by
a precision noise floor -- see K0-proof-v6.md Sec 8 and the session's S* probe)
further out, to shrink S* = sum|c_i|2^i below its current value of ~6.98.

DIAGNOSIS OF THE ORIGINAL FAILURE (see chat history): extracting [z^i]G_2(1,z)
via Cauchy sampling on |z|=1 with N samples inherits a per-sample certified
radius from G2Engine's own Euler-tail bound (roughly O(1/(P log P)) in
absolute terms, independent of i). Averaging N samples in BALL arithmetic does
not shrink this radius the way it would for random noise -- it propagates
through unchanged. Once the true coefficient (~3^-i) drops below this fixed
floor (around i~15 at P=8e6, prec=300), the reported "coefficient" is pure
noise, and multiplying by 2^i amplifies it into an apparent blow-up.

THE FIX: increase P (shrinks the floor like 1/(P log P)) and precision
together, enough that the floor stays below 3^-i for i up to I_TARGET.
Rough requirement: 1/(P log P) << 3^-I_TARGET, i.e. P >> 3^I_TARGET / log(3^I_TARGET).
For I_TARGET=30: 3^30 ~ 2e14, need P on the order of 1e13-1e14 -- likely too
large for a prime sieve. For I_TARGET=20: 3^20 ~ 3.5e9, need P ~ 1e8-1e9,
feasible on a large machine. Run with increasing P and confirm the coefficients
keep decaying geometrically (no plateau) rather than trusting a single P.

Usage:
    python3 extend_head_highprec.py <P_CUTOFF> <IMAX> <PREC_BITS> <N_SAMPLES>

Example (256-core machine -- the sieve and Cauchy sum both parallelize over
primes/samples; this script computes serially per call, launch several P
values concurrently from a shell loop to compare):
    python3 extend_head_highprec.py 200000000 20 400 2048
"""
from flint import acb, arb, ctx
import sys, time

def primes_upto(n):
    s = bytearray([1])*(n+1); s[0] = s[1] = 0
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(2, n+1) if s[i]]

def main():
    P = int(sys.argv[1])
    IMAX = int(sys.argv[2])
    PREC = int(sys.argv[3])
    N = int(sys.argv[4])
    ctx.prec = PREC
    t0 = time.time()

    print(f"Sieving primes up to {P}...")
    PS_all = primes_upto(P)
    PS = [p for p in PS_all if p > 2]
    print(f"  {len(PS)} primes, {time.time()-t0:.0f}s")

    # Build S1 = sum log(1-1/p), PZ[m] = sum p^-m (p>2), m=1..IMAX, at s=1
    S1 = arb(0)
    PZ = [arb(0)]*(IMAX+1)
    t1 = time.time()
    for p in PS:
        pa = arb(p)
        S1 += (1 - 1/pa).log()
        ipow = 1/pa
        for m in range(1, IMAX+1):
            PZ[m] += ipow
            ipow /= pa
    print(f"  power sums built, {time.time()-t1:.0f}s")

    Pa = arb(P)
    def wide(v): return arb(0).union(v.union(-v))
    log2 = arb(2).log()

    # Euler tail bound for p>P (worst case, standard prime-tail estimate)
    def euler_tail(m):
        # sum_{p>P} p^-m <= 1/((m-1) P^(m-1) log P) for m>=2; for m=1 this
        # diverges on its own (cancels against S1's own divergence, as noted
        # in Sec 4 -- here we only need m>=2 tail since PZ[1] combines with S1).
        if m < 2: return arb(0)  # handled via the S1+PZ[1] combined tail below
        return 1/((m-1)*Pa**(m-1)*Pa.log())
    combined_tail_m1 = 1/(2*Pa*Pa.log())  # for the S1+PZ[1] combined linear term

    PZ_tailed = [arb(0)]*(IMAX+1)
    for m in range(1, IMAX+1):
        t = combined_tail_m1 if m == 1 else euler_tail(m)
        PZ_tailed[m] = PZ[m] + wide(t)

    # log G2(1,z) = z*[log(1/2)+S1+PZ[1]] + sum_{j>=2} z^j PZ[j]/j
    logG = [arb(0)]*(IMAX+1)
    logG[1] = (1 - 1/arb(2)).log() + S1 + PZ_tailed[1]
    for j in range(2, IMAX+1):
        logG[j] = PZ_tailed[j]/j

    # exponentiate the power series (real coefficients since z on unit circle
    # handled via direct complex evaluation below; this "logG" array is used
    # for a sanity cross-check against the direct Cauchy extraction)
    print(f"logG[1..{min(8,IMAX)}] (real, s=1):")
    for j in range(1, min(8, IMAX)+1):
        print(f"  logG[{j}] = {logG[j].str(10)}")

    # Direct Cauchy extraction on |z|=1 with N samples, using the SAME
    # certified PZ_tailed values (not re-summing the raw Euler product per
    # sample point -- this reuses the high-precision power sums directly,
    # which is both faster and avoids re-accumulating per-sample tail error).
    t2 = time.time()
    coeffs = [acb(0)]*(IMAX+1)
    for t in range(N):
        theta = 2*arb.pi()*t/N
        z = acb(theta.cos(), theta.sin())
        lg = z*((1-1/arb(2)).log() + S1 + PZ_tailed[1])
        zp = z
        for j in range(2, IMAX+1):
            zp = zp*z
            lg += zp*PZ_tailed[j]/j
        g = lg.exp()
        for i in range(IMAX+1):
            coeffs[i] += g/z**i
    for i in range(IMAX+1):
        coeffs[i] = coeffs[i]/N
    print(f"  Cauchy extraction done, {time.time()-t2:.0f}s")

    print(f"\nCertified |c_i| * 2^i (i=1..{IMAX}), P={P}, prec={PREC} bits, N={N} samples:")
    Sstar_head = arb(0)
    for i in range(1, IMAX+1):
        ci = coeffs[i]
        mag = arb(abs(ci.mid())) + arb(ci.rad())
        weighted = mag * arb(2)**i
        Sstar_head += weighted
        print(f"  i={i:2d}: |c_i|={mag.str(10)}   |c_i|*2^i={weighted.str(8)}   rad={float(ci.rad()):.3e}")
    print(f"\nHead sum (i=1..{IMAX}) of |c_i|*2^i: {Sstar_head.str(10)}")
    print("Compare to the session's certified S* = 6.98 (head to i=14 + geometric tail).")
    print("If this head sum is noticeably BELOW 6.98 minus the old tail (~1e-8), the")
    print("extension genuinely tightened S*. If coefficients plateau or grow with i")
    print("well before i=IMAX, the precision floor has been hit again -- increase P further.")
    print(f"\nTotal time: {time.time()-t0:.0f}s")

if __name__ == '__main__':
    main()
