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
