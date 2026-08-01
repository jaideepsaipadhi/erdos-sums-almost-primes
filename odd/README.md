# The odd Erdős sums

    f_k^odd  =  sum over odd n >= 3 with Omega(n) = k of 1/(n log n)

CONJECTURE (Lichtman, 2026-07-29): f_k^odd is strictly decreasing for all k.

## Why this is the natural companion result

The main theorem disproves Banks-Martin: f_k is strictly *increasing* from
k = 6.  The suspicion is that the prime 2 is entirely responsible -- n = 2^k
dominates f_k, and removing it should restore the conjectured decrease.  If so
the pair of results says: Banks-Martin was right in spirit, and wrong only
because of a single prime.

## What transfers from the even case

MUCH OF THE MACHINERY ALREADY WORKS WITH p >= 3.  The manuscript's
normalisation pulls the p = 2 factor out as kappa(s)^z, so:

  * `cFac s = prod_{p>=3} (1 - p^-s)^-1` is ALREADY the odd Euler product,
    and its multipliability is already proved in Banksmartin/Basic.lean
  * `dConst`, `rhoConst`, `G2C` are all p >= 3 objects
  * beta_sweep.py, gamma2_sweep.py, the delta-table machinery and the
    criterion sweeps all operate on p >= 3 products

WHAT DOES NOT TRANSFER: the shape of the expansion.  For f_k the nearest pole
is at z = 2^s, giving f_k ~ 2^-k (a_1 k^2 + ...).  For f_k^odd it is at
z = 3^s, so the decay is 3^-k and the polynomial factor differs.  Proposition
2.5's exact decomposition has to be rederived, not merely recomputed.

Faster decay should make the error terms relatively smaller, so the criterion
may come out cleaner than the even case.

## Status

Nothing proved yet.  First task: establish numerically, to the precision the
existing pipeline achieves, that f_k^odd decreases over a useful range.

## Layout

    numerics/    computations for the odd case

## FINDING (first day): the odd case should be far easier

f_k^odd decays like 3^-k, so f_{k+1}/f_k -> 1/3 and there is no delicate
cancellation to resolve.  In particular the POINTWISE inequality

    c_{k+1}(s) <= c_k(s)     for all s >= 1,    c_k(s) = sum_{Omega(n)=k, n odd} n^-s

appears to hold for every k >= 2, with the worst case at s = 1:

    worst ratio over k = 2..10, as s -> 1+
      s=1.000   0.80034
      s=1.010   0.76951
      s=1.100   0.56334

Integrating over s in [1, inf) then gives f_{k+1}^odd < f_k^odd directly, with
NO error analysis: no delta-table, no criterion sweep, no S*, alpha_+ or Gamma.

k = 1 is the single exception -- pointwise domination fails at s = 1 exactly
(ratio 1.0957), because sum_{p>=3} p^-s diverges there.  But the integrated
values are 0.8143 vs 0.3735, a factor of two, so any crude bound settles it.

PROOF SKETCH
  1. k = 1: direct evaluation of the two integrals.
  2. k >= 2: pointwise domination.  c_k(s) = [z^k] prod_{p>=3}(1 - z p^-s)^-1,
     so the claim is a statement about the coefficients of an Euler product
     with all factors having their nearest singularity at |z| = 3^s >= 3.
     The 20% margin at the worst point suggests a crude Cauchy estimate on
     |c_k(s)| suffices.

This is a page, not a paper -- and correspondingly small to formalize.

## PROOF STRATEGY

Write c_k(s) = h_k(3^-s, 5^-s, 7^-s, ...), the complete homogeneous symmetric
function in the odd prime powers.  Two facts:

(1) h_{k+1} <= h_1 * h_k.
    Standard: h_1 h_k counts each degree-(k+1) multiset once per DISTINCT
    element it contains, hence at least once, so it dominates h_{k+1}.

(2) h_1 = P(s) = sum_{p>=3} p^-s, and P(s) <= 1 exactly when s >= 1.25
    (P(1.20) = 1.0697 + tail, P(1.25) = 0.9172 + 0.0073).

So for s >= 1.25, c_{k+1}(s) <= c_k(s) for EVERY k, immediately.

WHAT REMAINS: the compact interval s in [1, 1.25].  Numerically the worst
ratio there is 0.80 at s = 1 (over k = 2..10), so there is 20% margin.  This is
a bounded interval sweep of the same kind as beta_sweep.py -- not an asymptotic
argument.

k = 1 is separate: pointwise domination genuinely fails at s = 1 (ratio 1.0957),
so f_1^odd > f_2^odd must come from the integrated values, 0.8143 vs 0.3735.

STATUS: (1) and (2) are proved above.  The interval [1, 1.25] and the k = 1
case are open.

## CORRECTION: the s -> 1+ endpoint is not settled

The r_2 values quoted in Step 3 were computed with a finite prime cutoff P and
are NOT stable in P:

    s = 1.00   P=2e4: r_2 = 0.755   P=1e5: 0.800   P=5e5: 0.840   (climbing)
    s = 1.05   P=2e4: r_2 = 0.638   P=1e5: 0.664   P=5e5: 0.685   (climbing)

At s = 1 every c_k(1) diverges (c_1(1) = sum_{p>=3} 1/p), so r_2(1) is a ratio
of two divergent truncations and the numbers above mean nothing on their own.
At s = 1.05 the sums converge but the truncation error is still large at
P = 5e5, so those margins are unreliable too.

The pointwise claim c_{k+1}(s) <= c_k(s) is therefore ESTABLISHED only where
the truncation is under control -- comfortably for s >= 1.25 by Step 2, which
is unaffected -- and OPEN near s = 1, which is exactly where the integrand of
f_k^odd = int_1^inf c_k(s) ds is largest.

What is needed: the limiting behaviour of r_2(s) as s -> 1+, with a rigorous
tail bound on sum_{p>P} p^-s rather than a bare truncation.  The 3^-s heuristic
suggests r_2 -> something well below 1, but that is a guess until checked.

## What the certified scaffold shows

Running the odd prime zeta through certified.py's recursion, with the pole
intact:

    eps=0.5    P_k^odd: 0.496  0.148  0.035  0.008  0.002  0.000
    eps=0.1    P_k^odd: 1.642  1.423  0.872  0.427  0.179  0.068
    eps=0.01   P_k^odd: 3.806  7.341  9.578  9.523  7.706  5.296
    eps=0.001  P_k^odd: 6.094 18.667 38.344 59.435 74.185 77.707

Near the pole P_k^odd GROWS with k, peaking around k ~ log(1/eps).  That is the
(log 1/(s-1))^k / k! profile -- the same structure that drives f_k -> 1 in the
even case, and it survives removing p = 2 because sum_{p>=3} p^-s still
diverges at s = 1.

CONSEQUENCE: f_k^odd does NOT decay geometrically.  The earlier sections of
this README claimed otherwise on the basis of prime-truncated computations,
which destroy exactly this divergence.  Those claims are withdrawn.

The odd problem therefore has the same shape as the even one, and the section
2-7 apparatus is the right tool, with every constant recomputed for the p >= 3
Euler product.  The one place it should be easier is the tail bound: the even
case uses P(s) <= 2.78 * 2^-s for s >= 2, and the odd analogue is governed by
3^-s instead.

## RESULT: certified f_k^odd, k = 1..20

Calibration: f_1^odd = 0.91526880, against f_1 - 1/(2 log 2) = 1.636616 -
0.721348 = 0.915268.  The computation is correct.

    k    f_k^odd            f_k^odd - 1/2    (f_k^odd - 1/2) * 2^k
    1    0.915268803        4.153e-01        0.830538
    2    0.619685094        1.197e-01        0.478740
    3    0.546010011        4.601e-02        0.368080
    5    0.508737351        8.737e-03        0.279595
   10    0.500196851        1.969e-04        0.201575
   15    0.500005232        5.232e-06        0.171446
   20    0.500000153        1.529e-07        0.160296

STRICTLY DECREASING on [2,20], certified.

f_k^odd -> 1/2, from ABOVE.  The excess e_k = f_k^odd - 1/2 satisfies
e_{k+1}/e_k -> 1/2, so the rate is governed by the prime 2 even though 2 is
excluded from the sum -- the generating function's next singularity after the
pole at s = 1 is at z = 2^s.

CRUCIALLY, e_k * 2^k is DECREASING (0.83, 0.48, 0.37, ..., 0.160 at k = 20),
so e_k is slightly slower than c 2^-k: a decaying polynomial correction.

Contrast the even case, where f_k = 1 - 2^-k(a_1 k^2 + ...) and the polynomial
factor GROWS -- that competition is what makes f_k turn around at k = 6.  Here
the polynomial works the other way, so there is no competition and no expected
turning point.

The conjecture therefore looks not merely true but comfortably so.  What is
needed for a proof is the analogue of section 2's exact decomposition with
limit 1/2 rather than 1, and a criterion whose sign is then constant rather
than changing at a threshold.

## PROOF SHAPE (k = 2, the worst case)

Pointwise domination c_k(s) >= c_{k+1}(s) FAILS near the pole and holds away
from it.  The bad region shrinks rapidly with k:

    sign of c_k - c_{k+1} at s = 1 + eps
    eps      k=2  k=3  k=4  k=5  k=6  k=7
    0.001     -    -    -    -    +    +
    0.01      -    +    +    +    +    +
    0.05      +    +    +    +    +    +

So k = 2 is the worst case, with crossover at eps* = 0.025.  Splitting the
integral there:

    int over [1, 1.025]     =  -0.107585
    int over [1.025, inf)   =  +0.181261
    total                   =  +0.073676
    certified f_2 - f_3     =   0.073675     (agrees to 6 digits)

The positive part exceeds the negative by 68%.  A proof therefore needs:

  (a) an UPPER bound on |int_{[1,1+eps*]} (c_{k+1} - c_k)|, where the
      integrand is controlled by the (log 1/(s-1))^k / k! profile;
  (b) a LOWER bound on int_{[1+eps*,inf)} (c_k - c_{k+1}), where pointwise
      domination holds -- via h_1(s) <= 1 for s >= 1.25 and a bounded sweep
      on [1+eps*, 1.25];
  (c) (a) < (b), with 68% of margin at k = 2 and more for larger k since the
      bad region shrinks.

This is a finite, bounded argument -- much less than the even case's sections
2-7, because there is no threshold to locate: the inequality holds for every
k >= 2 with margin, rather than switching sign at k = 6.

## ANALYTIC STRUCTURE

Near the pole, P_odd(s) = log(1/(s-1)) - 1/2 + O(s-1), and c_k(s) ~ L^k/k!
with L = P_odd(s).  Hence

    c_{k+1}/c_k ~ L/(k+1) > 1   iff   L > k+1   iff   s - 1 < e^-(k+3/2)

so the crossover is at eps*(k) = e^-(k+3/2), shrinking geometrically:

    k        2        3        4        6        8
    pred  0.0302   0.0111   0.0041   0.00055  0.000075
    obs   0.025    ~0.005            ~0.0008

Under s = 1 + e^-t the bad region is t > k + 3/2, so to leading order

    negative mass = int_{k+3/2}^inf t^k e^-t / k! dt   (a Gamma tail)
    positive mass = 1 - that

    k        2        3        4        6        8
    tail  0.3209   0.3423   0.3575   0.3782   0.3918
    diff  0.3583   0.3154   0.2850   0.2437   0.2164

The leading-order difference is positive but SHRINKING in k, while the true
f_k - f_{k+1} shrinks like 2^-k.  So the leading term alone does not prove
positivity -- the margin must be tracked against the corrections, which is
exactly what section 2's exact decomposition does in the even case.

STATUS: the shape of the proof is clear and matches the certified numbers.
Making it rigorous needs the odd analogue of Proposition 2.5 -- an exact
identity for f_k^odd with all error terms explicit -- not an asymptotic
estimate.  That is the next real piece of work.

## THE REDUCTION (this is the right foundation)

Since prod_{p>=3} (1 - z p^-s)^-1 = (1 - z 2^-s) prod_p (1 - z p^-s)^-1,
extracting coefficients gives the EXACT identity

    c_k^odd(s) = P_k(s) - 2^-s P_{k-1}(s)

and integrating,

    f_k^odd = f_k - g_{k-1},        g_k := int_1^inf 2^-s P_k(s) ds

VERIFIED against the certified f_k^odd:

    k   g_{k-1}        f_k^odd + g_{k-1}   = f_k
    1   0.7213468320   1.6366156349          (= sum_p 1/(p log p))
    2   0.5251314683   1.1448165627
    3   0.4848249760   1.0308349869
    4   0.4777596782   0.9973413231
    5   0.4801403776   0.9888777290

The right column is the manuscript's f_k, including the dip below 1 before the
turnaround at k = 6.  The identity is exact.

CONSEQUENCE.  The odd conjecture becomes

    f_k^odd - f_{k+1}^odd = (f_k - f_{k+1}) + (g_k - g_{k-1})  >  0

The first bracket is -2^{-k-1} Crit(k), NEGATIVE for k >= 6 by the main
theorem.  So the odd result is exactly the statement that g increases faster
than f decreases -- a comparison between the unweighted and the 2^-s-weighted
integrals of the SAME P_k.

This is much better than rebuilding sections 2-7 for the p >= 3 product:
everything already proved about P_k, the delta table, the coefficient bounds
and the criterion applies unchanged.  The single new object is g_k.

CERTIFIED DIFFERENCES (all positive, ratio -> 1/2 from below):

    k     f_k^odd - f_{k+1}^odd    ratio
    2     +7.3675e-02              0.2493
    5     +4.7383e-03              0.4369
   10     +1.0251e-04              0.4739
   15     +2.6661e-06              0.4868
   19     +1.5545e-07              0.4937

The ratio increases monotonically toward 1/2 and never approaches 1, so unlike
the even case there is no competition between a geometric factor and a growing
polynomial -- hence no turning point.

NEXT: an exact decomposition of g_k with explicit error terms, i.e. the
analogue of Proposition 2.5 for the weighted integral.  Then the criterion for
the odd case is Crit(k) < 2^{k+1}(g_k - g_{k-1}), and the main theorem's
machinery bounds the left side already.

## g_k: STRUCTURE

Certified g_k = int_1^inf 2^-s P_k(s) ds for k = 0..20 (odd/numerics/g_k.py).
g_k dips below 1/2 at k = 2 and returns:

    k     g_k                  (g_k - 1/2) 2^k
    0     0.7213475204         +0.2213
    2     0.4848250909         -0.0607
    5     0.4847544275         -0.4879
   10     0.4981045526         -1.9409
   15     0.4998593480         -4.6089
   20     0.4999917617         -8.6385

CONSISTENCY CHECK: recovering f_k = f_k^odd + g_{k-1} reproduces the
manuscript's values exactly, including the dip below 1 and the turnaround --
f_4 = 0.99734, f_5 = 0.98888, f_6 = 0.98875, f_7 = 0.99102, ... f_20 = 0.99999.
So the identity and both computations are mutually confirming.

EMPIRICAL LEADING TERM.  Fitting (g_k - 1/2) 2^k = -c k^2:

    k=10  c = 0.019409      k=17  c = 0.020943
    k=14  c = 0.020252      k=20  c = 0.021596       log 2 / 32 = 0.021661

converging from below, four digits by k = 20.  So

    g_k = 1/2 - (log2 / 32) k^2 2^-k (1 + o(1))       [CONJECTURAL]

Note log2/32 = (1/8)(log2/4) while a_1 = d(log2/4) with d = 0.3787, so g's
analogue of d would be exactly 1/8.  That is clean enough to be real, but it is
a numerical fit, NOT derived -- deriving it is the next piece of work and is
what an exact decomposition of g_k would establish.

With it, the odd criterion becomes explicit:
    f_k^odd - f_{k+1}^odd = (f_k - f_{k+1}) + (g_k - g_{k-1})
and both brackets have k^2 2^-k leading behaviour with known coefficients.

## CORRECTION: log2/32 was a coincidence

Extending g_k to k = 40 shows A(k) = -(g_k - 1/2) 2^k is NOT c k^2 with
c = log2/32.  A(k)/k^2 climbs steadily through that value and past it:

    k        16       20       24       28       32       36       40
    A/k^2  0.02072  0.02160  0.02238  0.02307  0.02367  0.02420  0.02466
    A-c0k^2  -0.242   -0.026   +0.415   +1.103   +2.055   +3.284   +4.800

with c0 = log2/32 = 0.021661.  The four-digit agreement at k = 20 was the
residual passing through zero, not convergence.

Second differences of A, which would be the constant 2c if A ~ c k^2:

    k        20       25       30       35       40
    2c    0.05696  0.05881  0.06007  0.06097  0.06161

still drifting upward -- the signature of a k log k term.  So g_k has the same
shape as f_k: a k^2 term plus a k log k correction, matching the even case
where E(k) is controlled by D(k) = log2 k log(k+1) + 1.

No clean closed form for the leading coefficient.  An exact decomposition of
g_k, with error terms bounded the way section 4 bounds delta_m, is what the
odd proof needs.

## CORRECTION: the reduction is for verification, not for the proof

Writing (f_k^odd - 1/2)2^k = 2A(k-1) - (a_1 k^2 + E(k)), with
A(k) = -(g_k - 1/2)2^k, the two terms on the right BOTH grow like k^2 and
nearly cancel:

    k      2A(k-1)    observed    cancellation
   16       9.2178    0.168166        55:1
   18      12.1048    0.163363        74:1
   20      15.4393    0.160296        96:1

and the ratio grows like k^2 -- about 500:1 by k = 40.

So a proof routed through f_k^odd = f_k - g_{k-1} would have to control both
f_k and g_k to relative precision O(1/k^2) merely to see the sign of their
difference.  That is HARDER than the even case, not easier.

Computed directly on the p >= 3 Euler product there is no cancellation:
f_k^odd - 1/2 is O(2^-k) on its own.

REVISED RECOMMENDATION.  Build the odd analogue of sections 2-7 directly on
the p >= 3 product -- which is what cFac, G2C, dConst and rhoConst in
Banksmartin/Basic.lean already are, since the manuscript's normalisation
pulls the p = 2 factor out separately.  Keep the reduction as a cross-check:
it is how f_k, f_k^odd and g_k were mutually confirmed above.

(An earlier section of this README recommended the reduction as the
foundation.  The cancellation analysis shows that was wrong.)

## DERIVED: the odd Proposition 2.5

Write prod_{p>=3}(1 - z p^-s)^-1 = zeta(s)^z H(s,z), so

    H(s,z) = (1 - 2^-s)^z prod_{p>=3} [(1 - z p^-s)^-1 (1 - p^-s)^z]

analytic in |z| < 3^s.  THIS IS THE STRUCTURAL DIFFERENCE from the even case:
with p = 2 removed, z = 2 lies strictly inside the domain of analyticity
instead of on the singularity, so there is no k^2 factor.

Substituting u = log zeta(s) and expanding eps = e^-u + gamma e^-2u + ...,
the contributions organise by powers of e^-u:

  order e^-u :   sum_j h_j(1) = H(1,1) = 1/2                    [the limit]
  order e^-2u:   2^-(k+1) [ d_s H(1,2) + 2 gamma H(1,2) ]       [the 2^-k term]

with H(1,2) = (1/4) prod_{p>=3} (1-1/p)^2/(1-2/p) = 1/(4 C_2) = d = 0.3786950,
and d_s log H(1,2) = 2 log 2 - 2S,  S = sum_{p>=3} log p/((p-1)(p-2)).

    f_k^odd = 1/2 + d (log 2 - S + gamma) 2^-k + O((3/8)^k)

PREDICTED  d(log2 - S + gamma) = 0.15563271

VERIFIED against the certified B(k) = 2^k (f_k^odd - 1/2).  Richardson
extrapolation, B_inf = (B_{k+1} - r B_k)/(1-r):

    r        k=16       k=18       k=19
    2/3    0.160183   0.158227   0.157586
    3/4    0.157522   0.156515   0.156231     <- flattest, -> 0.15563
    1/2    0.162844   0.159939   0.158941

The r = 3/4 row converges on the predicted value from above.  The next
correction is order e^-3u, which relative to the 2^-k normalisation decays
like (3/4)^k -- self-consistent.

CONSEQUENCE FOR THE CONJECTURE.  Since the leading coefficient is a positive
constant with no polynomial factor,

    f_k^odd - f_{k+1}^odd = d(log2 - S + gamma) 2^-(k+1) + O((3/8)^k) > 0

for all large k, with no threshold.  Contrast the even case, where the k^2
factor competes with 2^-k and produces the turnaround at k = 6.  Making this
rigorous needs explicit error control on the O((3/8)^k), the analogue of
section 4's bound on delta_m.

## DERIVED: the odd Proposition 2.5

Write prod_{p>=3}(1 - z p^-s)^-1 = zeta(s)^z H(s,z), so

    H(s,z) = (1 - 2^-s)^z prod_{p>=3} [(1 - z p^-s)^-1 (1 - p^-s)^z]

analytic in |z| < 3^s.  THIS IS THE STRUCTURAL DIFFERENCE from the even case:
with p = 2 removed, z = 2 lies strictly inside the domain of analyticity
instead of on the singularity, so there is no k^2 factor.

Substituting u = log zeta(s) and expanding eps = e^-u + gamma e^-2u + ...,
the contributions organise by powers of e^-u:

  order e^-u :   sum_j h_j(1) = H(1,1) = 1/2                    [the limit]
  order e^-2u:   2^-(k+1) [ d_s H(1,2) + 2 gamma H(1,2) ]       [the 2^-k term]

with H(1,2) = (1/4) prod_{p>=3} (1-1/p)^2/(1-2/p) = 1/(4 C_2) = d = 0.3786950,
and d_s log H(1,2) = 2 log 2 - 2S,  S = sum_{p>=3} log p/((p-1)(p-2)).

    f_k^odd = 1/2 + d (log 2 - S + gamma) 2^-k + O((3/8)^k)

PREDICTED  d(log2 - S + gamma) = 0.15563271

VERIFIED against the certified B(k) = 2^k (f_k^odd - 1/2).  Richardson
extrapolation, B_inf = (B_{k+1} - r B_k)/(1-r):

    r        k=16       k=18       k=19
    2/3    0.160183   0.158227   0.157586
    3/4    0.157522   0.156515   0.156231     <- flattest, -> 0.15563
    1/2    0.162844   0.159939   0.158941

The r = 3/4 row converges on the predicted value from above.  The next
correction is order e^-3u, which relative to the 2^-k normalisation decays
like (3/4)^k -- self-consistent.

CONSEQUENCE FOR THE CONJECTURE.  Since the leading coefficient is a positive
constant with no polynomial factor,

    f_k^odd - f_{k+1}^odd = d(log2 - S + gamma) 2^-(k+1) + O((3/8)^k) > 0

for all large k, with no threshold.  Contrast the even case, where the k^2
factor competes with 2^-k and produces the turnaround at k = 6.  Making this
rigorous needs explicit error control on the O((3/8)^k), the analogue of
section 4's bound on delta_m.

## THE ODD THEOREM: complete in outline

Two ranges, overlapping:

  k = 1..20    certified values (odd/numerics/fodd_run.py), strictly decreasing
  k >= 11      the leading term dominates the Cauchy-bounded remainder

For the second range: Htilde(s,z) = H(s,z)(1 - z 3^-s) is analytic in
|z| < 5^s, so Cauchy on |z| = R gives |[z^k] Htilde(1,z)| <= M_R R^-k with

    M_3.5 =  85.795     M_4.0 = 171.022     M_4.5 = 344.449

(sup attained at z = -R on the negative real axis, where (1-1/p)^z grows;
48-point scan, needs an interval sweep for rigour.)

The requirement is that the remainder be under beta 2^-k / 3, with
beta = d(log2 - S + gamma) = 0.15563271:

    k        need         M_4.5 4.5^-k
   10     5.066e-05        1.012e-04     no
   11     2.533e-05        2.248e-05     OK
   12     1.267e-05        4.996e-06     OK
   15     1.583e-06        5.482e-08     OK
   20     4.947e-08        1.109e-10     OK

so K0^odd = 11 at radius 4.5 (12 at radius 4), and the margin grows by a
factor of ~2.25 per step.

REMAINING FOR RIGOUR:
  * M_R by interval arithmetic rather than a point scan -- the same
    computation beta_sweep.py does for the even case, on Htilde instead
  * the certified sweep already covers k = 1..20, well past K0^odd = 11
  * assemble: [1,20] certified, [11,inf) analytic, no gap

Note how much smaller this is than the even case: no delta table, no criterion
sweep over thousands of k, no threshold hunt.  The reason is structural --
with p = 2 removed, z = 2 lies strictly inside the domain of analyticity of H
rather than on its boundary, so the leading behaviour is a constant times 2^-k
instead of k^2 2^-k, and nothing competes with it.
