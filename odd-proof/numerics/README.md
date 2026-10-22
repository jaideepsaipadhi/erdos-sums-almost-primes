# odd-proof/numerics

Certified inputs for `odd-proof/PROOF.md`.  Each script prints an interval or an
explicit upper bound; the committed `.log` beside it is that run.

## Constants of (5.1)

| script | constant | method |
|---|---|---|
| `hcoeff_recursion.py` | `sum_{i<=16} \|g_i\| 3^i <= 8424` | interval recursion, 1600 s-boxes |
| `mr_deriv_sweep.py` | `sup_{\|z\|=4.5} \|G_2\| <= 1.97e6` | 200 theta x 40 s boxes |
| `s0_recursion.py`, `s0_cauchy.py` | `S_0 <= 44.5987` | first-order pole; head by recursion, tail by Cauchy |
| `s1_recursion.py`, `s1_cauchy.py` | `S_1 <= 486.1945` | second-order pole; head by recursion, tail by Cauchy |
| `cn_certified.py` | `CN <= 367.8435` | odd Euler-product recursion (Moebius prime zeta) + Cauchy tail |
| `nearu_certified.py` | `NEARU <= 26.0962` | exact head to k=400 + explicit envelope |
| `ce_taylor.py` | `CE <= 5.48910` (log: `5.4890962927`) | Taylor model in eps, whole range at once |

Together these give `C = CE S/18 + S_0/2 + 5*590/64 + CN + NEARU = 4857.9`,
and (5.1) is stated with `C = 4900`.

## The sign of the `h_j` and the range of (5.1)

`absratio.py` records a defect in the near-range step as the manuscript states
it.  That step bounds `sum_j int_0^3 u^{k-j}/(k-j)! |h_j(s(u))| J(u) du` by the
*signed* coefficient identity `sum_j u^{k-j}/(k-j)! h_j(s(u)) = P_k^odd(s(u))`,
which needs `h_j >= 0`.  The `h_j` alternate:

    h_1(s) = P_3(s) - log zeta(s) = log(1 - 2^-s) - sum_{m>=2} P_3(ms)/m < 0

for every `s`, and at `s = s(3)` the coefficients run
`1, -0.762, +0.377, -0.126, +0.0353, ...`.  The script computes both sums; the
signed one reproduces `P_k^odd(s(3))` to 267 digits and peaks at `367.8435` at
`k = 11`, which is `CN`, so the comparison is against the right quantity.

The inflation is confined to small `k`.  `A_k 3^k` peaks at `15329` at `k = 12`,
falls back under `CN` at `k = 24`, and is `27.63` at `k = 59` — so `CN` has
13.3x of slack where the bound is actually used.  The analytic branch is
invoked only for `k >= K0 = 59`; monotonicity for `k <= 75` comes from the
certified sweep, which never calls on the remainder bound.  **No certified
constant moves:** `CN`, `C = 4900` and `K0 = 59` all stand.  What has to change
is the *range* on which (5.1) is asserted, and the near-range argument itself,
which must be redone on `|h_j|` (majorant `H_o^+ = H_o e^{-2 h_1 z}`, whose
coefficients are non-negative, with the `s`-range split: the majorant's crude
per-term bound stops being integrable around `s ~ 15`, where the true quantity
is already negligible).  A single all-`k` constant would instead be about
`19819`, which would push `K0` to `63`.

## Margin under (5.1)

The 0.9% of margin there is an artefact of the `NS = 1600` setting, not of the
method: `hcoeff3200.log` halves the box width and gives head `7890.6376` in
place of `8423.9098`, hence `S_2 <= 13881` and `C = 4695.2` — 4.2% of margin.
The head is still falling at `NS = 3200`.  Nothing downstream moves either
way: `K0 = 59` at `C = 4900`, at `C = 4700` and at `C = 4695.2`, and
`MR <= 4900` stays true a fortiori, so the finer run is recorded here as
headroom under the stated budget rather than substituted into it.  It answers
the obvious question about that margin: the 0.9% is the box width, not the
method running out of room.

## Certified values of g_k

`fodd_run.py` at 1000-bit precision; `fodd75.log` reaches k = 75, which is what
section 6 needs (the analytic threshold is K0 = 59).

**Reproduced 2026-10-15, byte-identical across all 75 values.**  The run takes
about 95 minutes, which is longer than some environments allow a single job to
live, so `fodd_run.py` now also accepts a panel range and `fodd_combine.py`
assembles the pieces -- the same split `certified.py`/`combine.py` already use
for the unrestricted case:

    python3 fodd_run.py 75 1000 0 27        # -> ochunks/o0000_0027.txt
    python3 fodd_run.py 75 1000 27 54       # ... any partition of [0,335)
    python3 fodd_combine.py 75 1000         # checks coverage, adds tails

`fodd_combine.py` refuses to report unless the chunks cover every panel with
no gap and no overlap, and it adds the two tail balls once, after summing.
Chunks already on disk are skipped, so a re-run costs nothing and an
interrupted sweep resumes.

Panel cost is very uneven -- about 0.7s each for the first fifty and about 20s
each thereafter -- so equal-width chunks are not equal-time ones.

## Reproducing

    pip install python-flint sympy      # s1_cauchy.py needs sympy as well

Every log below was regenerated from a clean checkout on 2026-10-14 and
matched the committed file exactly, to every printed digit:

    python3 ce_taylor.py                      -> ce_taylor.log
    python3 nearu_certified.py                -> nearu.log
    python3 cn_certified.py                   -> cn.log
    python3 s0_recursion.py 16                -> s0_head.log
    python3 s0_cauchy.py                      -> s0_cauchy.log
    python3 s1_recursion.py                   -> s1_head.log
    python3 s1_cauchy.py                      -> s1_cauchy.log
    python3 hcoeff_recursion.py 16 1600       -> hcoeff2.log
    python3 hcoeff_recursion.py 16 3200       -> hcoeff3200.log
    python3 mr_deriv_sweep.py                 -> mr_deriv_sweep.log

Two of those arguments are not the defaults, and running the script bare does
NOT reproduce its log:

  * `s0_recursion.py` defaults to NMAX = 40; the log of record is NMAX = 16,
    the split point used by s0_cauchy.py for the tail.
  * `hcoeff_recursion.py` defaults to NMAX = 40, NS = 40.

`mr_deriv_sweep.log` and the `fodd*` logs were captured with `nohup ... 2>&1`,
so their progress lines are interleaved with the results; compare the result
lines only.

## Notes

`S_0`, `S_1`, `CN`, `NEARU` and `CE` quantify what earlier drafts of section 5.1
left as "(lower order)".  `CE` in particular is not lower order: it multiplies
the leading term, and moving from the implicit `CE = 3` to the true `5.48910`
is what takes `C` from 2402.3 to 4857 and `K0` from 57 to 59.

`ce_taylor.py` supersedes two earlier attempts (a point sweep and a box sweep)
that could not certify the range: the constants are ratios in which zeta's pole
cancels, and interval evaluation on boxes of `s` loses that cancellation.
