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
    python3 crossval_refined.py

`cchunks/` (407 MB of PREC=1400 panels feeding `ci_certified.json`) is not in
the repository; `ci_certified.py` regenerates it.

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
