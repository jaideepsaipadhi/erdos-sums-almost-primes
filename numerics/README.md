# Certified numerics

Everything the Lean development assumes rather than proves comes from here.
`erdos_sums_increase_from_six` is conditional on a `NumericalFacts` structure;
these are the Arb ball computations that justify its fields.  The analytic
reduction is machine-checked, these are not, and that division is the one
Caveat 1.3(b) of the manuscript draws.

## Directories

    bm-rebuild-v21/   the current pipeline: c_i, beta_i, gammahat_i, the delta
                      table, and the criterion sweeps.  Start here.
    k0-run/           the earlier end-to-end run (MASTER_CHECK.py, and the
                      parallel delta and s-uniform drivers).  Its own README
                      describes that pipeline.
    delta-job/        the sharded delta computation as dispatched.
    verify.py         checks the outputs against theorems proved in Lean.

## Which artefact feeds which NumericalFacts field

| field | artefact | script |
|---|---|---|
| `d_enclosure`, `rho_enclosure` | computed inline | `bm-rebuild-v21/ci_certified.py` |
| `Sstar_bound`   | `ci_certified.json`   | `ci_certified.py` |
| `alpha_bound`   | `beta_certified.json` | `beta_sweep.py` |
| `Gamma_bound`   | `gamma_constant.json` | `gamma2_sweep.py` |
| `source_bound`  | `m1_constant.json`, `tail_constants.json` | `crit_refined.py` |
| `phi_at_k1`, `phi_mono` | `k1_far_range.log` | `k1_far_range.py` |
| `sweep_low`  [6,199]    | `certificate*.json`  | `certificate.py`, `lowk_verify.py` |
| `sweep_mid`  [78,899]   | `crit_78_734.json` (78-734, refined) + `crit_certified.json` (735-899, unrefined) | `crit_refined.py` |
| `sweep_high` [900,2439] | `crit_900_2439.json` | `sweep_900_2439.py` |

Supporting: `bhat_signed_N60.json` (b-hat_i), `gamma2_certified.json`
(gammahat_i), `delta_table.jsonl` (delta_m), `shards/` (256 shards;
`merge_verify.py` reassembles).

## Checks against the formalization

    cd bm-rebuild-v21 && python3 ../verify.py

Each check is a theorem proved in `Basic.lean` applied to the Arb output:
Theorem 4.1's bound |delta_m| <= log2 m log(m+1) + 1 over 2441 entries;
`A2m_le` (A2_m <= (m+1)/2); `geom_two_three`; the Cauchy tails; Gamma's
recomposition; and the sweep coverage.  A bug that passes these has to be
consistent with proved mathematics.

## The contour radius

The tail estimates use analyticity of G2 in |z| <= 2.9 (`M1_R2.9`,
`M2sup_R2.9`).  The Lean wide-radius chain runs at |z| <= 29/10, so this is
formally proved, not only argued in the manuscript.

## Provenance of the three constants: RESOLVED

The two *sweep* scripts shipped with defaults that do not reproduce their
stored tables -- the sup over s in [1,2] tightens with the box count, and the
production runs used far more boxes than the defaults.  Both are now pinned in
`__main__`, and the regenerated tables are uniformly at or below the stored
ones.

    ci_certified.py    N=30, P=2e6, prec=400     reproduces EXACTLY
                       (also passes its own checks sum c_i = 1/2 and
                        sum c_i 2^i = d, the two identities proved in Lean)
    beta_sweep.py      P=1e5, boxes=1600, prec=300
    gamma2_sweep.py    P=1e5, boxes=800,  prec=300

CONSEQUENCE -- all four headline constants improve on the manuscript:

    alpha_+   15.5716  ->  15.4257
    Gamma    105.4060  -> 104.5196
    K0             79  ->  78   (k=77 gives -7.85, k=78 gives +0.91)
    K1           2440  -> 2433  (margin 138 rather than 89)

Every downstream bound therefore holds with more room, and coverage is
unaffected.  The criterion sweep is `crit_78_734.json`.

## Reproducing

    pip install python-flint
    cd bm-rebuild-v21
    python3 ci_certified.py
    python3 beta_sweep.py
    python3 gamma2_sweep.py
    bash run_delta_job.sh && python3 merge_verify.py
    python3 crit_refined.py 78 734
    python3 sweep_900_2439.py
    python3 k1_far_range.py
    python3 crossval_refined.py ../certificate.json

`cchunks/` (407 MB of PREC=1400 panels feeding `ci_certified.json`) is not in
the repository; `ci_certified.py` regenerates it.

## Supporting and cross-check scripts

The table above lists what backs each `NumericalFacts` field.  These are the
rest of the pipeline and its validation layer, which that table does not name:

| script | role |
|---|---|
| `certified.py`, `runner.sh`, `combine.py` | the panel run: `runner.sh` drives `certified.py` over `cchunks/`, resumable; `combine.py` reads the chunks back and reports the enclosures and the monotonicity verdicts |
| `bm-rebuild-v21/delta_table.py`, `delta_shard.py`, `delta-job/` | the contiguous certified `delta_m` table, sharded and resumable, at precision ~2.2m + 300 bits; `merge_verify.py` reassembles and checks |
| `bm-rebuild-v21/conv_tail.py` | certified `Delta(k) = sum_i 2^i c_i delta_{k-i}` from the table plus a tail ball |
| `bm-rebuild-v21/crit_assembly.py` | assembles the criterion from the pieces.  Its header constants are marked PROVISIONAL; `crit_refined.py` is the one of record |
| `measure_impact.py` | sensitivity study: rebuilds `U`, `V`, `S*` with the interval radii shrunk, to see how much of each constant is genuine width |

Two of these are independent cross-checks rather than parts of the chain, and
are worth knowing about when the certified route is the thing in question:

| script | checks |
|---|---|
| `bm-rebuild-v21/ci_crosscheck.py` | recomputes `c_i` by direct Euler-product evaluation on \|z\|=1 with Cauchy/FFT extraction, taking the prime tail from `mpmath.primezeta` -- a different code path and a different library from the certified log-series route |
| `bm-rebuild-v21/delta_ref.py` | a reference implementation of the GLW Lemma 3.3 quantities written straight from the paper, against which the optimised `delta_*` route is compared |

Neither is certified, and nothing depends on them; they exist to disagree
with the certified route if it is wrong.

## Reproduced from clean

Rerun on 2026-10-14 against the committed artifacts:

| command (from `bm-rebuild-v21/`) | result |
|---|---|
| `python3 k1_far_range.py` | `k1_far_range.log` reproduced identically: `K1 = 2433`, certified margin `138 +/- 0.602`, derivative gap `145.256` |
| `python3 crit_refined.py 78 734` | `sweep_78_734.log` reproduced identically (`k=78: crit_lower = 0.91`, `k=734: 33754.05`), and `crit_78_734.json` regenerated **byte-identical** to the committed file |
| `python3 crossval_refined.py ../certificate.json` | gate passes 101/101, worst deviation ratio `0.0001` against an expected `~0.01` |
| `python3 beta_sweep.py` (7m09s) | `beta_certified.json` and `bhat_signed.json` regenerated **byte-identical**; invariant `sup >= |value at s=1|` holds for all i; assembled `alpha_+ = 15.425661`, matching the paper and `NumericalFacts.alpha_bound` |
| `python3 gamma2_sweep.py` (5m54s) | `gamma2_certified.json` and `gamma2_s1_signed.json` regenerated **byte-identical**; invariant holds; `sum_{i<=24} ghat_i 2^i = 203.11826010925864`, the stored `head`, so `Gamma = (head+tail)/2 = 104.51964366990232` |

`alpha_+` is not the bare weighted sum of `beta_certified.json`: it is
`(sum_{i=1..30} beta_i 2^i)/2 + M1 (2/2.9)^31 / (1 - 2/2.9) / 2`
(`k1_far_range.py` lines 56-61).  Dropping the tail gives 15.3849 and looks
like a mismatch; with it the value is exact.

### Two stored constants no script regenerates

    m1_constant.json     M1_R2.9     = 2543.6624045073563   -> alpha_+ tail
    gamma_constant.json  M2sup_R2.9  = 19881.155667290404   -> Gamma tail
                         (and Gamma itself, = (head + tail)/2)

Both are contour sups on `|z| = 2.9`.  They are read by `crit_refined.py`,
`crossval_refined.py`, `k1_far_range.py` and `crit_assembly.py`, and feed two
constants in the trusted base, but nothing in the repository computes them:
`grep M2sup *.py` returns nothing, and no script opens either file for
writing.  Everything else above regenerates; these do not, so they cannot be
checked from here.

The odd case has the analogue and it does have a script --
`odd-proof/numerics/mr_deriv_sweep.py`, a theta x s interval sweep of
`sup_{|z|=R} |d_s^a Htilde|`, which reproduces its log exactly.  That is the
template for the missing one.

Until it exists, `bm-rebuild-v21/m1_crosscheck.py` gives an independent
NON-CERTIFIED estimate of the same two sups, by a different route: it builds
`G_2(s,z) = ((s-1) zeta(s))^z H_o(s,z)` directly on `|z| = 2.9` and
differentiates in `s` by finite differences, so an error in the derivative
algebra cannot be shared with whatever produced the stored values.  It
self-tests first, extracting `c_i = [z^i] G_2(1,z)` by FFT and comparing with
`ci_certified.json` (worst absolute deviation 7.2e-07 over i <= 7), and
refuses to report if that fails.

    python3 m1_crosscheck.py            # ~1 min

Result: `sup |d_s G_2| ~ 129` against the stored `M1 = 2543.66`, and
`sup |d_s^2 G_2| ~ 3.5e3` against the stored `M2sup = 19881.16`.  Both stored
constants bound the estimate, by factors of about 20 and 6 -- the slack a
triangle-inequality derivation would produce, and in the safe direction.  The
profile in `s` is monotone decreasing from `s = 1`, so the maximum is at the
endpoint and there is no interior spike to miss.

This corroborates; it does not certify.  Double precision, a finite grid, and
primes truncated at 1e5 can only fail to find a violation.



The certificate path is an argument, not a default: `crossval_refined.py`
looks for `certificate.json` in the working directory, and it lives one level
up, so the bare command fails with FileNotFoundError.

The acceptance gate passing is what discharges the PROVISIONAL marker in
`crit_refined.py`'s header and the "pending the [810,899] slice" wording that
`crossval_refined.py` printed; the slice is covered by `crit_certified.json`
(735-899) and the regenerated constants give `K0 = 78`.

Not yet rerun here: `ci_certified.py` (regenerates 407 MB of panels),
`beta_sweep.py`, `gamma2_sweep.py`, and the delta-table job.

## The quadrature constant

`certified.py` uses `CQ = 10 * (64/15) * rho^(-2*NGL) / (1 - rho^(-2))` with
`NGL = 52` nodes.  That is the Gauss bound of Trefethen, *Is Gauss quadrature
better than Clenshaw--Curtis?*, SIAM Rev. 50 (2008), 67-87, Theorem 4.5
eq. (4.14) -- stated there as `rho^(-(2n+2))` with `I_n` built on `n+1` nodes,
which is the same quantity -- carried in ATAP as Theorem 19.3, times a factor
10 of margin.  Checked against the source on 2026-10-14; the paper's appendix
cites both.

The four `certificate*.json` files predate that check and still carry the
caveat "verify exact statement before citation" in their `caveats` field.
They are left as they are on purpose: `certificate.py` hashes the payload
*including* `caveats`, so editing the text by hand would break the stored
`sha256_of_payload_without_hash`.  All four currently verify, and the wording
will correct itself the next time they are regenerated.
