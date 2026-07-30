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
