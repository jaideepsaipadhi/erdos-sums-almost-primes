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
