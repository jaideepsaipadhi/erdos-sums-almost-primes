# Certified numerics

Everything the Lean development assumes rather than proves comes from here.
`erdos_sums_increase_from_six` is conditional on a `NumericalFacts` structure;
these are the Arb ball computations that justify its fields.  The analytic
reduction is machine-checked, these are not, and that division is the one
section 8 of the manuscript draws (not "Caveat 1.3(b)", which does not exist
in the manuscript -- see README.md).

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
| `sweep_mid`  [78,899]   | `crit_78_734.json` (78-734, refined) + `crit_650_899.json` (728-899, fallback) | `crit_refined.py`, `crit_fallback.py` |
| `sweep_high` [900,2439] | `crit_900_2439.json` | `sweep_900_2439.py` |

### The 735-899 slice: what used to back it, and what does now

This table used to credit `crit_refined.py` for `crit_certified.json` as well.
That was wrong, and the error mattered because `crit_certified.json` was the
only artifact covering 735-899 -- the slice between the refined run and
`[900,2439]`.  Solving for the inputs that reproduce it (exactly, at k = 650,
735 and 899) gives

    |E1(k)| <= alpha*k + beta,   alpha = 15.5716454,  beta = -39.60918

-- i.e. `crit_assembly.py`'s linear bound, whose `crit_sweep(650, 899)` is
hardcoded in its `__main__`, run with the manuscript's **superseded** `alpha_+`
(the paper now states `alpha_+ <= 15.425661`) plus a **negative intercept the
manuscript does not state at all**.  `crit_900_2439.json` fits the same pair,
exactly, at k = 900, 1500 and 2439.  So neither fallback certificate came from
the script credited here, and `sweep_900_2439.py` does not reproduce its own
committed output: rerun, it gives min 10115.96 where the committed file had
9724.11.

Nothing was false -- the larger `alpha` outweighs the negative `beta`, so both
committed files were *more* conservative than the certified inputs require, and
every positivity claim held a fortiori.  The defect was provenance and
declaration: a referee following this repo could not regenerate either file,
and `crit_assembly.py` run as committed produces `crit_sweep.json`, whose
`ALPHA, BETA = "15.374", "-37.226"` its own docstring calls "clearly
uncertified" and which crosses zero at 726 rather than 735.

Both are now regenerated from committed scripts and declared inputs only:

| file | script | result |
|---|---|---|
| `crit_650_899.json` | `crit_fallback.py 650 899 crit_650_899.json` | positive on **[728,899]**, min 27.65 at 728; at k=735 it is 362.62 against the old file's 43.04 |
| `crit_900_2439.json` | `python3 sweep_900_2439.py` | positive on [900,2439], min 10115.96 (was 9724.11) |

`crit_fallback.py` is `sweep_900_2439.py` generalized to an arbitrary range,
and it reproduces that script's committed-script output on [900,2439] **bit for
bit** -- that is its regression test, and the reason to trust it on [650,899].
It uses the per-`i` fallback `E1b` built from `beta_certified.json` plus the
`M1` tail, needs no `beta` at all, and reports its own `alpha_+` envelope
(`15.4256608821`) against `uv_constants.json` as a cross-check.

Two consequences worth keeping:

  * **the union now overlaps instead of abutting.**  It used to work only
    because `crit_certified.json` covered exactly 735-899, with no slack on
    either side; `verify.py` checked that file's zero crossing and not its
    load-bearing role, so a one-off change would have opened a silent gap.  The
    blocks are now `[78,734] [728,899] [900,2439]`, and `verify.py` checks the
    union for gaps directly.
  * `crit_certified.json` is kept, superseded, as the baseline the newer runs
    improve on. `verify.py` checks that `crit_650_899.json` is nowhere weaker
    than it (250 shared k, none weaker).

Supporting: `bhat_signed_N60.json` (b-hat_i), `gamma2_certified.json`
(gammahat_i), `delta_table.jsonl` (delta_m), `shards/` (256 shards;
`merge_verify.py` reassembles).

## Section 7, the general principle: `genP_check.py` and `boundary_check.py`

These two back the general-`P` material in section 7 of the manuscript and
nothing else.  **They are mpmath, not Arb** -- no ball arithmetic, no
certification -- so they are verification of formulas, not certified inputs,
and no `NumericalFacts` field depends on them.  Read them that way.

| script | what it checks | log |
|---|---|---|
| `genP_check.py` | the interior case `q >= 3`: the constants `c_0` and `c_2` of Proposition 7.2(iv), against `f_k^P` computed independently | `genP.log` |
| `boundary_check.py` | the boundary case `q = 2`: that the ratio to the all-primes case tends to `prod_{p in Q}(1-2/p)`, which is what the reduction in section 7 needs | `boundary.log` |

`genP_check.py` with `Q = {2}` is the calibration that makes the rest
meaningful: `P = {p >= 3}` is the case the paper proves, so `c_2` there must
reproduce the certified `beta` and `H_P(1,2)` the certified `d`.  It gives
`0.155632714` against `beta = 0.15563259` and `0.378695020` against
`d = 0.3786950315`, both inside the `~1e-7` error bar the p-sums carry (run to
`X = 2e6` with the PNT tail `1/X`; the product tail
`prod_{p>X}(1-1/p)^2/(1-2/p) = 1 - O(1/(X log X))` is deliberately NOT added,
and is what the last digits of `H_P(1,2)` against `d` reflect).

Read the right column.  In `genP.log` the final `/c_2` ratio is `1.13` at
`k = 14` for `Q = {2}` but `1.003` for `Q = {2,3}`, and the first is not a
failure: at `q = 3` the subleading term is the `O(k^3 3^-k)` one whose constant
the paper bounds by `4900`, so `f_k` is nowhere near its asymptotic at `k = 14`
and the integral is too expensive to push far enough.  For `q = 3` the
meaningful check is the constants themselves against the certified `d` and
`beta`, not the `f_k` column; for `q >= 5` the `f_k` column converges quickly
(relative deviation `~0.9*(2/3)^k`) and is the end-to-end test.

The all-primes side of `boundary_check.py` has its own check, independent of
anything in section 7: fitting `f_k - 1 ~ -C k^a 2^-k` to the committed
`boundary.log` values gives `a = 2.298, 2.279, 2.261, 2.247, 2.234` across
consecutive pairs from `k = 24` to `44`, decreasing monotonically toward `2`.
That is the factor `k^2` of Gorodetsky--Lichtman--Wong, reproduced here from
scratch, and it is the reason to believe the `f_k^all` column at all.

Two traps, both of which cost time here:

  * **the convergence is slow and one-sided, and the printed `3.2e-4` is NOT an
    error bar.**  The ratio approaches its limit from below with an `O(1/k)`
    correction, so the raw value is useless as a check -- at `k = 44` it is
    `0.31209` against a predicted `1/3`, and for `Q = {5}` it is `0.572066`
    against `0.6`.  Read the two-term `1/k` extrapolation.  But that is a
    three-parameter fit through three points, so it has zero residual and its
    closeness to the prediction is a property of the basis, not a measured
    error.  Judge it by stability instead:

    | Q | two-term, three windows | one-term | `log k/k` basis | spread |
    |---|---|---|---|---|
    | `{3}` | `0.333227`, `0.333171`, `0.333447` | `0.336577` | `0.329517` | ~1% |
    | `{5}` | `0.600056`, `0.600424`, `0.600537` | `0.603172` | `0.596605` | ~0.6% |

    The `1/k` fits are stable under changing the window and the alternatives
    are not, which is the argument for that basis -- but the choice is not
    independent of the conclusion, since `eq:GLW-asymptotic`'s `O(k log k)`
    cancels in the ratio only under a stronger form of the hypothesis being
    tested.  The script's own `k*(E_Q - ratio)` column drifts monotonically
    (`1.043 -> 0.935` for `Q={3}`) with no flattening; do not read it as
    converged.  Below about `k = 20` nothing is readable at all.
  * **`maxdegree` is quadrature depth, not digits**, and the working precision
    has to grow with `k`: the substitution forms `1 + e^-t`, which rounds to
    exactly `1` at the top of the `t`-range unless `dps > ~0.45*t`, and then
    `zeta` is evaluated at its pole.  `dps_for` handles this; do not lower it.

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

## Conjecture 7.1 beyond the two proved cases

**Half of this section is now a theorem, and the labels in the log predate it.**
Corollary 7.3 of the manuscript proves that `f_k^P` is eventually strictly
decreasing for EVERY admissible `P` with `q >= 3`.  So in the table below the
rows `drop {2}`, `drop {2,3}`, `drop {2} u INF` and `drop {2,5} u INF` are no
longer open cases -- they are controls, and they pass.  `conj71_explore.log`
still prints `(OPEN: says decreasing)` beside them because the run predates
the corollary; the log is a run record and is left as it stands.  What remains
open is only the `q = 2` direction: `drop nothing`, `drop {3}`, `drop {5}`,
`drop INF`.

`conj71_explore.py` tests the general principle numerically for sets of primes
the paper does not cover.  Removing finitely many primes keeps the complement
thin trivially, so these are legitimate instances, and two of them probe
exactly what neither proved case does: a `q = 2` set with a nontrivial
complement, and a `q >= 5` set.

    python3 conj71_explore.py 14 300        # about 5 minutes, -> conj71_explore.log

| P | q | Conjecture 7.1 | observed | turns at |
|---|---|---|---|---|
| all primes | 2 | increasing | increasing | k = 6 |
| drop {2} | 3 | decreasing | decreasing | never |
| drop {3} | 2 | increasing | increasing | k = 9 |
| drop {2,3} | 5 | decreasing | decreasing | never |
| drop {5} | 2 | increasing | increasing | k = 7 |

| drop INF | 2 | increasing | increasing | k = 13 |
| drop {2} u INF | 5 | decreasing | decreasing | never |
| drop {2,5} u INF | 11 | decreasing | decreasing | never |

`INF` is the primes at index `2^n` -- `3, 7, 19, 53, 131, ...` -- an INFINITE
thin complement (`sum 1/p` about `0.56`).  That class is the one the
conjecture's hypothesis actually names; every finite complement above sits in
a strictly smaller class, so these three are the first tests inside the real
hypothesis.  The `q = 2` case needed `k = 24` to settle: it turns at `k = 13`
and then rises for eleven consecutive steps.

All eight agree.  The control matters as much as the open cases: the full set
turns at `k = 6`, which is exactly the threshold Theorem 1.1 proves, so the
pipeline reproduces a known answer before being trusted on unknown ones.

Two things the table shows that the conjecture does not say.  The turnaround
index depends on `P` and moves later as more mass is removed: 6 for the full
set, 7 dropping `{5}`, 9 dropping `{3}`, and 13 for the infinite complement,
whose `sum 1/p` is about `0.56`.  Removing a smaller prime, or more primes,
delays the crossover.  And the `q >= 3` cases decrease from
`k = 2` onward with no turnaround at all, where the `q = 2` cases all decrease
first and turn.

This is evidence, not a certificate.  It reuses the certified panel and
quadrature machinery but NOT its error terms, which were derived for the full
and odd cases; the script reports midpoints.  Extending the certified error
analysis to general `P` would be needed before any of this could be stated as
a result.

### It agrees with `genP_check.py`, which shares no code with it

The two general-`P` pipelines are independent implementations: this one runs
flint/arb over `certified.py`'s panels, `genP_check.py` runs mpmath over the
`prod L_p` factorization with `primezeta`.  On the two `P` both compute:

| P | k | this (arb panels) | `genP_check.py` (mpmath) | difference |
|---|---|---|---|---|
| drop `{2}`   | 10 | `0.500196851` | `0.500196850821` | `1.8e-10` |
| drop `{2}`   | 14 | `0.500010707` | `0.500010709023` | `2.0e-9`  |
| drop `{2,3}` | 10 | `0.333522321` | `0.333522321396` | `4.0e-10` |
| drop `{2,3}` | 14 | `0.333344998` | `0.333345000033` | `2.0e-9`  |

Both are midpoint computations with no error term, so this is agreement rather
than verification -- but they fail differently if either is wrong, and they do
not.  Check any new general-`P` work against both.
