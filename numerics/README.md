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

**`S*` was stated 3.3e-5 too small.**  The certified sum is
`6.97633273` -- head `i <= 30` alone is `6.97633205`, tail `6.7e-7` -- so the
`S* <= 6.9763` that stood in the paper, in `SstarConst` and in both
`Sstar_bound` fields was not an upper bound: `6.97633` had been rounded down
where an upper bound must round up.  `U` and `V` beside it in the same
proposition are rounded up correctly (`0.08436`, `1.907462`, against certified
`0.0843596939` and `1.9074617159`), so this was an isolated slip rather than a
convention.  Now `6.9764` in all three places.

Nothing downstream moves.  `k1_far_range.py` computes `S*` itself and never
reads the stated constant, so every certified number -- `phi(2440)`, `K0`, the
criterion sweeps -- was always computed against `6.97633`.  What was wrong was
the *stated* bound, and in Lean that mattered more than it looks: a hypothesis
no real `S*` can satisfy makes the theorem that assumes it vacuous exactly
where it is applied.

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

`cchunks/` (407 MB of PREC=1400 panels) is not in the repository.  Those are
`certified.py`'s quadrature panels, regenerated by `certified.py`/`combine.py`
-- NOT by `ci_certified.py`, which this file used to say.  `ci_certified.py`
computes the `c_i` straight from the Euler product by the log-series and exp
recurrence in its header: no panels, no quadrature, **3 seconds**.

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

### Two stored constants: now certified

    m1_constant.json     M1_R2.9     = 2543.6624045073563   -> alpha_+ tail
    gamma_constant.json  M2sup_R2.9  = 19881.155667290404   -> Gamma tail
                         (and Gamma itself, = (head + tail)/2)

Both are contour sups on `|z| = 2.9`.  They are read by `crit_refined.py`,
`crossval_refined.py`, `k1_far_range.py` and `crit_assembly.py`, and they feed
the trusted base as the Cauchy tails `|beta_i| <= M1 2.9^-i` and
`|gammahat_i| <= M2sup 2.9^-i` (the second is `verify.py`'s "Cauchy tail at
2.9" check).  For a long time nothing in the repository produced them: they
were stored with no derivation on file.

`m1_certified.py` now does, by the method of the odd case's
`mr_deriv_sweep.py` -- an interval sweep in `theta` and `s`, with the
`s`-derivatives taken analytically rather than by finite differences.  Two
things differ from that template.  The factor `((s-1) zeta(s))^z`, absent in
the odd case, contributes `z A(s)` to `log G_2` and is handled by the same
certified Stieltjes expansion `beta_sweep.py` uses.  And the sweep is a branch
and bound rather than a uniform grid, because a uniform grid must be fine
enough for its worst box everywhere, and the worst box here is at `s = 1`,
`theta = 0`, where the `p = 3` Euler factor's pole sits at `|z| = 3` and the
enclosure of `1 - z 3^-s` is nearly as wide as it is long.

    python3 m1_certified.py 64 32 1000 100000 300 26      # setting of record

It self-tests before sweeping: it evaluates `G_2(1, 2)` from its own formula
and compares with `sum_i c_i 2^i` assembled from `ci_certified.json` and
`tail_constants.json`, and refuses to report if the two intervals are
disjoint.  The tie-in is taken at `|z| = 2`, not at 2.9: the certified `c_i`
tail at 2.9 is `(2.9/3)^31/(1-2.9/3)`, about 10, far too wide to test
anything, while at 2 it is about `1e-6`.

Result: `sup |d_s G_2| ~ 129` against the stored `M1 = 2543.66`, and
`sup |d_s^2 G_2| ~ 3510` against the stored `M2sup = 19881.16`.  Both stored
constants are upper bounds, by factors of about 20 and 5.7 -- the slack a
triangle-inequality derivation produces, and in the safe direction.  Both sups
are attained at `s = 1`; for `d_s G_2` the maximising point on the circle is
`z = -2.9` (theta = pi), which is worth knowing because a sweep seeded only
near theta = 0 will miss it.

`m1_crosscheck.py` remains as an independent NON-CERTIFIED estimate by a
different route -- double precision, finite differences in `s`, a finite grid
-- and agrees: 128.83 and 3509.32.  Its own self-test is a RELATIVE
comparison against `ci_certified.json` despite printing the word "absolute",
so it is sensitive to `PCUT`; run it at the default `1e5`, where it passes at
`7.2e-07`.

Two traps this exercise produced, both worth knowing before touching the
script:

  * `1/(den*den)` is not `inv*inv`.  Near the `p = 3` pole the ball
    `den = 1 - z 3^-s` has radius comparable to its own modulus, so `den*den`
    straddles zero and the quotient blows up by three orders of magnitude --
    733632 where the true term is 2120.  Squaring the inverse, a ball bounded
    away from zero, is conditioned correctly.
  * the worklist is a stack, so the traversal is depth first.  A partial run
    reports the maximum over the boxes visited SO FAR, which can look
    converged and be wrong; the progress lines are marked `[PARTIAL]` for
    that reason.  Only the final block is a bound.




The certificate path is an argument, not a default: `crossval_refined.py`
looks for `certificate.json` in the working directory, and it lives one level
up, so the bare command fails with FileNotFoundError.

The acceptance gate passing is what discharges the PROVISIONAL marker in
`crit_refined.py`'s header and the "pending the [810,899] slice" wording that
`crossval_refined.py` printed; the slice is covered by `crit_certified.json`
(735-899) and the regenerated constants give `K0 = 78`.

Rerun 2026-10-15: `ci_certified.py` (3 s), all 31 coefficients identical to
the committed `ci_certified.json`.  `beta_sweep.py` and `gamma2_sweep.py` were
already regenerated byte-identical, as the table above records -- this
sentence had contradicted it.

Still not rerun here: the delta-table job.  It is feasible but long: the
shards are stride-sharded and resumable, and `delta_arb` costs about 5.8 s at
`m = 1046`, 14.7 s at `m = 1500`, scaling near `m^2.6`, so `m = 2440` is about
52 s and the range 1046-2440 is roughly 9.4 core-hours.

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
