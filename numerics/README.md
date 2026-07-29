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
| `phi_at_k1`, `phi_mono` | stdout | `k1_far_range.py` |
| `sweep_low`  [6,199]    | `certificate*.json`  | `certificate.py`, `lowk_verify.py` |
| `sweep_mid`  [79,899]   | `crit_certified.json`, `crit_sweep.json` | `crit_refined.py` |
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

## WARNING: NMAX in beta_sweep.py

Raising `NMAX` from 30 does NOT simply extend the table -- it degrades the
i <= 30 coefficients by a factor of 10 or more (head sum 31.06 -> 44.09) and
makes alpha_+ worse.  The cause is not understood.  The tables are valid only
at the NMAX they were computed with, and the generators now write into the
working directory, so a careless rerun overwrites certified data.  Back up
`beta_certified.json` before touching it.

## Reproducing

    pip install python-flint
    cd bm-rebuild-v21
    python3 ci_certified.py
    python3 beta_sweep.py
    python3 gamma2_sweep.py
    bash run_delta_job.sh && python3 merge_verify.py
    python3 crit_refined.py 79 899
    python3 sweep_900_2439.py
    python3 k1_far_range.py
    python3 crossval_refined.py

`cchunks/` (407 MB of PREC=1400 panels feeding `ci_certified.json`) is not in
the repository; `ci_certified.py` regenerates it.
