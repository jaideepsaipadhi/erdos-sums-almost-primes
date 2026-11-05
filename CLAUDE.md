# erdos-sums-almost-primes

Lean 4 formalization of the analytic reduction for the Banks–Martin / Erdős
almost-prime sums, plus the Arb-certified numerics it imports as hypotheses.

- `paper/proof.tex` — the manuscript (with J. D. Lichtman)
- `Banksmartin/`, `Odd/` — the Lean development
- `numerics/` — unrestricted case; `odd-proof/numerics/` — odd case

## Git

Commit and push without asking. Work on a branch, never directly on `main`;
open a PR rather than merging. Do not wait for the stop hook to prompt.

Keep scratch files out of the working tree — use the session scratchpad
directory, not the repo. `.gitignore` covers the usual offenders, but an
auto-commit will sweep up anything it misses.

## The constants must agree in three places

Every certified constant appears in `paper/proof.tex`, in `odd-proof/PROOF.md`
or `numerics/`, and in the Lean `NumericalFacts` / `OddNumericalFacts`
structures. Section 8 of the paper asserts that the formalization proves the
paper's reductions, so these cannot drift apart.

When a regenerated value is sharper than the one in print, either change all
three together, or leave the stated value alone and record the sharper one as
headroom with a sentence saying why. **Never sharpen the paper alone** — that
replaces a harmless conservatism with a real defect.

Currently stated conservatively on purpose, each with the reason in the text:

| Stated | Sharper value available | Why not substituted |
|---|---|---|
| criterion threshold `2440` | `2433` (margin 135) | Lean `NumericalFacts.phi_at_k1`, `theorem_7_1`'s `[2440, ∞)` |
| `\|c_i\| < 354.36·3^-i` | `44.5987·3^-i` via Lemma 3.7(i) + `Σ₀` | Lean cCoeff tail lemma, `Basic.lean:6768` (uses `4.2^i`) |
| `S₂ ≤ 14414` (NS=1600) | `13881` (NS=3200, `hcoeff3200.log`) | `K₀ = 59` either way; pure margin under `MR ≤ 4900` |
| `C_N ≤ 367.8436` in the near range | `34.14` for `k ≥ 59` (`nearabs.log`) | one constant serves both the signed and the absolute sum; keeps `MR ≤ 4900` and the ledger unchanged |

The margin at `k = 2433` was 139 before the three numeral corrections to
`lem:phi-base`; `check_paper_phi.py` now recomputes it from the certified
constants and reads it out of the manuscript, so the two cannot drift again.

### Stated constants must round UP, and nothing used to check that

`Σ_1` was in print as `486.1945` while `s1_cauchy.log` certifies
`486.19450958…`, and `C_N` as `367.8435` against `cn.log`'s `367.84350183…`.
Both were rounded **down**, so the manuscript asserted bounds its own
certificates do not establish — and all three existing guards passed, because
they only ever compared the paper against itself. `check_proof_spine.py` now
parses `s0_cauchy.log`, `s1_cauchy.log`, `cn.log`, `ce_taylor.log` and
`nearu.log` and fails if any stated numeral is below the certified value.
Verified against a deliberately reintroduced `486.1945`.

### `Sigma_2 <= 14414` is a TWO-LOG assembly with 0.16 of margin

It is the largest constant in the paper and carries `4395.55` of the `4857.88`
ledger — 90% of it — and it is not a single logged number:

    head j <= 16   8423.9098   hcoeff2.log      (interval recursion, 1600 s-boxes)
    tail j > 16    5989.9336   mr_deriv_sweep.log: G_2 <= 1967216.5 at R = 4.5,
                               tail = G_2 (3/R)^17 / (1 - 3/R)
    total         14413.8434   against the stated 14414 — margin 0.157

So it is the second-tightest constant after `C_E`. `check_proof_spine.py` now
recomputes the assembly from both logs. Note `hcoeff2.log`'s own trailing
`C_2 = 10.8165` / `K0 = 33` lines are a DIFFERENT quantity — don't mistake
them for `Sigma_2`. The `NS = 40` boxes behind the tail are coarse and likely
several-fold loose; that direction is safe.

### `C_E <= 5.48910` is the tightest constant in the paper

The four suprema of `eq:CE-def` are attained at `s(3)` and give
`C_E = 5.4890955…`, so the printed bound has about `4e-6` of margin — roughly
`8e-7` relative, against 0.86% for the ledger and 8% for `eq:odd-base-59`. It
is valid (`ce_taylor.log`: `5.4890962927`), but it is the one constant with no
headroom, so any change to the Taylor-model settings must be re-checked
against it rather than assumed safe.

### The remainder bound is stated on `k >= 59` in all three places

Not conservatism, but a property of the **method**, not of the quantity. The
near range bounds a sum of **absolute** values and the `h_j` alternate in sign
(`h_1 = Π(s) − log ζ(s) < 0` always), so it goes through a majorant that is
loosest where `a(s) = 2|h_1(s)|` is largest — at the left end of the **`s`**
range, not at small `k`. The certified bound exceeds `C_N 3^-k` for exactly
`9 ≤ k ≤ 25`, peaking at `699.87` at `k = 14` — run
`nearabs_certified.py 60 8.0 220 60 60 400 1`, i.e. the settings of record
with `K0 = 1`. Coarser settings give a looser bound (`724.55` at `NGRID=120,
MMAX=50`), so quote only the settings-of-record figures. Do not quote `15329` here:
that is `absratio.py`'s **pointwise** sum at `u = 3`, a different quantity from
the integral that `eq:odd-nearabs-certified` bounds. `k ≥ 26` would serve; 59
is stated because it is the only range in which (5.1) is ever applied. The three places are `prop:odd-remainder` and
`eq:odd-intro-expansion` in the paper, `(5.1)` in `odd-proof/PROOF.md`, and
`OddNumericalFacts.remainder` in Lean. **Do not widen any of them to `k ≥ 1`**:
a single all-`k` constant is about `19819`, which moves `K₀` to 63 and past
`sweep_low`'s `k ≤ 58`, and since no instance of the structure is ever
constructed, a too-wide field would make the theorems vacuous rather than
false and nothing would catch it.

`Odd/Basic.lean`'s `fOdd_expansion_final` still carries `hk : 1 ≤ k` and should
tighten to `59 ≤ k`; it is unbuilt here, so the binder was left alone and the
reason recorded in its docstring.

## The committed certificates, and what actually backs each sweep range

`numerics/verify.py` must be **run from `numerics/bm-rebuild-v21/`** — its
docstring says so, and from anywhere else it silently skips the criterion
sweeps (`load()` returns `None` and the loop `continue`s) while two unrelated
checks error out. Run correctly it passes all 12. Don't report it as broken
without checking the directory first.

What backs `eq:full-sweep-ranges`, regenerated 2026-11-05:

| artifact | what it holds | range | script |
|---|---|---|---|
| `numerics/certificate.json` | `f_k` enclosures, compared pairwise | `k = 2..500` | `certificate.py` |
| `bm-rebuild-v21/crit_78_734.json` | refined criterion `> 0` (min 0.91) | `78..734` | `crit_refined.py 78 734` |
| `bm-rebuild-v21/crit_650_899.json` | fallback criterion `> 0` from 728 (min 27.65) | `728..899` | `crit_fallback.py 650 899` |
| `bm-rebuild-v21/crit_900_2439.json` | fallback criterion `> 0` (min 10115.96) | `900..2439` | `sweep_900_2439.py` |

The blocks now **overlap**: `[78,734] [728,899] [900,2439]`. They used to abut
exactly at 735 with no slack, and `verify.py` checked only the zero crossing of
the file carrying that slice, so a one-off change could have opened a silent
gap. `verify.py` now checks the union for gaps directly.

### Both fallback certificates were regenerated; the old ones had the wrong provenance

**This section used to claim `crit_78_734.json` and `crit_certified.json` have
"no generating script in the repository". That was wrong both ways.**
`crit_refined.py` takes `klo khi outfile` and generates the first — with its run
of record committed beside it as `sweep_78_734.log`. And the two *fallback*
certificates were generated by a script, just not the one `numerics/README.md`
credited: solving for the inputs that reproduce them gives, exactly,

    |E1(k)| <= alpha*k + beta,   alpha = 15.5716454,  beta = -39.60918

(the criterion sees `alpha*(3k+1) + 3*beta`, per `crit_assembly.py`'s own
comment; the fit is exact at `k = 650, 735, 899` for `crit_certified.json` and
at `k = 900, 1500, 2439` for `crit_900_2439.json`). That is
`crit_assembly.py`'s linear bound — its `__main__` hardcodes
`crit_sweep(650, 899)` — run with the manuscript's **superseded** `alpha_+`
(the paper states `alpha_+ <= 15.425661`) plus **a negative intercept the paper
never states**. Consequences:

- `sweep_900_2439.py` did **not** reproduce its own committed output. Rerun it
  gives min `10115.96` where the committed file had `9724.11`.
- `crit_assembly.py` run as committed produces `crit_sweep.json` instead, whose
  `ALPHA, BETA = "15.374", "-37.226"` its own docstring calls "clearly
  uncertified"; those are *smaller* than certified, i.e. optimistic, and it
  crosses zero at 726 rather than 735. Do not reuse that script's constants.

**Nothing was false.** The larger `alpha` outweighs the negative `beta`, so both
committed files were more conservative than the certified inputs require and
every positivity claim held a fortiori. The defect was provenance and
declaration — a referee could not regenerate either file, which matters now
that Section 8 cites the repo by URL.

`crit_fallback.py` is the repair: `sweep_900_2439.py` generalized to an
arbitrary range, using the per-`i` fallback `E1b` from `beta_certified.json`
plus the `M1` tail, with **no `beta` at all**. Its regression test is that it
reproduces `sweep_900_2439.py` on `[900,2439]` **bit for bit** — check that
before trusting any change to it. It also prints its own `alpha_+` envelope
(`15.4256608821`) against `uv_constants.json`'s `15.425661`.

Regenerating on declared inputs is **strictly stronger**, not a concession:
`crit_650_899.json` is positive from `k = 728` rather than 735, is nowhere
weaker than the file it replaces (250 shared `k`, checked in `verify.py`), and
at the critical `k = 735` gives `362.62` against the old `43.04` — a factor of
8.4. `crit_certified.json` is kept, superseded, as the baseline.

The stated range in `eq:full-sweep-ranges` was deliberately **left at
`78..899`** rather than widened to `728`: per the round-up discipline above, the
extra 7 values of `k` are recorded here as headroom instead of being substituted
into the manuscript.

## Section 7: point one is closed, point two is reduced

Section 7 used to list two open points plus a third it resolved inline. The
first is now a theorem and the second is reduced to a single case.

The tool for both is one factorization. With
`L_p(s,z) = (1-p^-s)^z (1 - z p^-s)^-1`, so that
`log L_p = sum_{m>=2} (z^m - z) p^-ms / m`,

    H_P(s,z) = prod_{p in P} L_p(s,z) * prod_{p notin P} (1 - p^-s)^z.

Everything `P`-dependent sits in the second product, and the first is
`P`-independent and converges for any `P` whatever. That is what makes the
general case tractable at all.

**Point one (interior case `q >= 3`) is Proposition 7.2 + Corollary 7.3**, and
it gives the full constants:

    f_k^P = prod_{p notin P}(1-1/p) + c_P 2^-k + o(2^-k),
    c_P   = H_P(1,2) (gamma + (1/2) d_s log H_P(1,2)).

Three things worth not rediscovering:

- **The thin-complement hypothesis does TWO jobs, not one.** The old text said
  it was load-bearing at exactly one step (positivity). It is also what makes
  the *leading* constant positive: the limit is `prod_{p notin P}(1-1/p)`,
  which is `0` unless `sum_{p notin P} 1/p < infty`. The sparse examples
  (`P = {2}`, `{2,3}`) are the degenerate case of that product, not a separate
  phenomenon.
- **The natural error term is `o(2^-k)`, not `O(3^-k)`.** A quantitative
  remainder needs `sum_{p notin P} (log p)^2/p < infty`, which thin complement
  does NOT give. Monotonicity only needs the sign of the `2^-k` coefficient, so
  the qualitative statement is the right one. Do not "strengthen" it to a rate.
- The proof needs `R` with `2 < R < q`, which is why it says nothing at `q = 2`.

**Point two (boundary case `q = 2`) is reduced, not closed.** Comparing the
factorization for `P` and for all primes,

    H_P(s,z) / H(s,z) = prod_{p notin P} (1 - z p^-s),    |z| < 2^s,

and `q = 2` forces `2 notin Q`, so every complement prime is `>= 3` and the
ratio extends continuously to the critical point `(1,2)` with value
`prod(1 - 2/p) > 0`. Both `H` and `H_P` blow up there; the ratio does not.
So IF the `k^2` coefficient involves the analytic factor only through its value
at `(1,2)` and not its `s`-derivatives, the whole boundary case follows from
all primes alone -- and that is **known to hold in the all-primes case
itself**, since GLW's `a_1 = d log2/4` is exactly `H_o(1,2) log2/4` (see "the
boundary numerator is an interior object" below). What is left is that the
same form holds with a general numerator, plus the existence of a `k^2`
expansion for general `q = 2` at all; neither follows from `eq:GLW-asymptotic`,
which is the single case `Q` empty.

**The `s`-derivatives do not have to be excluded.** If the coefficient is
`A Phi(1,2) + B d_s Phi(1,2)` with `A, B` independent of `P`, then because
`Phi_P = Phi * E_Q` and `d_s log E_Q(1,2) = sum_{p in Q} 2 log p/(p-2)` (a
convergent sum of POSITIVE terms), the coefficient for `P` is `E_Q(1,2)` times

    A Phi(1,2) + B d_s Phi(1,2) + B Phi(1,2) sum_{p in Q} 2 log p/(p-2),

so it vanishes only if that sum equals one exact constant `kappa` fixed by the
all-primes data. Non-cancellation therefore holds for every admissible `P` with
`q = 2` outside at most one level set of an explicit functional of `Q`, and for
all of them at once if `kappa <= 0`. So the remaining point is: get the form of
the `k^2` coefficient for all primes. Say it that way, not "prove the boundary
case".

The numerical test does NOT settle `B = 0`, and don't claim it does. A second
complement is not discriminating either: the `Q = {3}` residual of `3.2e-4`
implies a shift of only `1.6e-4` for `Q = {5}`, which is below the
extrapolation error. Distinguishing `B = 0` from small `B` needs better
extrapolation (more and larger `k`), not another `Q`.

### Four traps in the Section 7 write-up, all hit once

- **`H_P` must be defined by the regularized product, never by
  `zeta^-z prod_{p in P}(1 - z p^-s)^-1`.** The second is `0` at `s = 1` --
  `zeta(1)^-z = 0` -- and `s = 1` is where every constant in the section is
  evaluated, so that version makes the factorization false and `H_P(1,1)`,
  `H_P(1,2)`, `c_P` all undefined. `eq:HP-def` is the definition; the
  `zeta^-z` form is an identity for `s > 1` only. A referee caught this after
  it had compiled cleanly through four builds.
- **`R` must be taken in `(2,3)`, not `(2,q)`.** The step bounding the
  `O(3^-m)` terms by `O(3^-k sum (3/R)^j) = O(R^-k)` is FALSE for `R >= 3`
  (at `R = 3.5`, `k = 40` the ratio is 3300), which `q >= 5` would permit.
  `R < 3` makes the geometric sum dominated by its last term. The conclusion
  `o(2^-k)` survives either way, which is why it passed inspection.
- **`1/p <= (log p)/p` fails at `p = 2`** (`log 2 = 0.693`), and `2` is in `Q`
  for every `P` with `q >= 3`. Use `1/p <= (log p)/(p log 3)` for `p >= 3` and
  split off `p = 2`.
- **A three-parameter fit through three points has no residual**, so its
  agreement with a prediction is not an error bar. Quote the spread across
  fitting bases instead: for the boundary ratio the `1/k, 1/k^2` basis gives
  `0.33317 / 0.33323 / 0.33345` across three windows (stable, `5e-4` of `1/3`),
  while `log k/k` gives `0.32952` and the one-term fit `0.336577` -- so the
  honest uncertainty is about `1%`, not `3.2e-4`. The script's own
  `k*(E_Q - ratio)` column drifts `1.043 -> 0.935` without flattening; don't
  present it as if it had converged.

### The boundary numerator is an interior object, and GLW's constant is its value

Two identities worth keeping. Separating the single factor `L_2` in
`eq:HP-def` gives, exactly,

    H_P(s,z) = H_{P \ {2}}(s,z) / (1 - z 2^-s),

so for all primes `H = H_o/(1 - z 2^-s)`: the entire `z`-singularity at
`z = 2^s` is that one explicit pole and its numerator is the ODD product. The
numerator belongs to a prime set with least element `>= 3`, so Proposition 7.2
applies to it -- the boundary case's crux is an interior object.

And GLW's `k^2` coefficient is exactly that numerator's value: `eq:d-def`'s `d`
is `eq:H-odd` at `(1,2)`, so `a_1 = d log2/4 = H_o(1,2) log2/4`, with no
`s`-derivative and no prime sum. Contrast `beta = d(gamma + (1/2) d_s log
H_o(1,2))`, which carries both. That contrast is the reason to think the form
is structural, and it is what makes the `B = 0` case of the reduction the
expected one. The predicted general coefficient is then
`a_1 prod_{p in Q}(1 - 2/p) > 0`.

### The two Section 7 scripts are mpmath, NOT Arb

`numerics/genP_check.py` and `numerics/boundary_check.py` are ordinary
floating-point. They carry no certificate, no `NumericalFacts` field depends on
them, and the paper says so explicitly. Do not let them drift into the
certified-constants ledger.

`genP_check.py` at `Q = {2}` is the calibration: `P = {p >= 3}` is a case the
paper proves, so it must return the certified `d` and `beta`, and it does
(`0.378695020` vs `0.3786950315`, `0.155632714` vs `0.15563259`, both inside
the `~1e-7` p-sum error bar). Run that before trusting any other output.

Two traps that cost real time:

- **Working precision must grow with `k`.** Both scripts substitute
  `s = 1 + e^-t`; at the top of the `t`-range that rounds to exactly `1` and
  `zeta` is then evaluated at its pole. `dps_for` sets it; don't lower it.
  `maxdegree` is mpmath's quadrature depth, not digits (4 and 5 agree to 6
  digits, 3 does not).
- **Boundary convergence is slow and one-sided.** The ratio rises to its limit
  with an `O(1/k)` correction: at `k = 44` it is `0.31209` against `1/3`, which
  looks like a refutation and is not. The two-term `1/k` extrapolation through
  `k = 36,40,44` gives `0.3332266`, relative error `3.2e-4`. Below `k ~ 20`
  nothing is readable. Quote the extrapolation, and call it evidence -- it
  cannot distinguish "no `s`-derivative terms" from "they cancel for this `Q`".

## `source_bound` is already derived; don't list it as open

Checked 2026-10-22. `NumericalFactsFull` has **no `source_bound` field**, and
`erdos_sums_increase_from_six'` discharges the obligation outright:
`source_bound_full` (`Basic.lean:14093`) applies `source_bound_derived`
(`:10002`) with the `E_1` hypothesis supplied by `E1k_le_alpha` (`:14052`, a
proved theorem), at the call site `:14326`, taking every remaining hypothesis
from `NumericalFactsFull` fields. So the Cauchy estimate behind `source_bound`
is proved in Lean; it is an aggregate ASSUMPTION only on the plain
`NumericalFacts` route, where what replaces it is the seven coupling fields
`M0_bound`, `g_deriv`, `g_deriv_bound`, `alpha_dom`, `Sstar_dom`, `UV_bound`,
`Eexp_bound` -- boxed suprema and finite sums, i.e. the easy direction.

`source_bound` was traded for finer, more checkable assumptions. It is NOT
blocked on certified-integration machinery, and `TRUSTED-BASE.md` said twice
that it was (both corrected). `remainder` is the one in that position; do not
name the two together.

## `remainder` already has a Lean derivation, wired to nothing

`Odd/Basic.lean`'s `fOdd_expansion_final` proves a statement of exactly the
shape of `OddNumericalFacts.remainder`. Verified 2026-10-22: **no term-level
application of it exists** -- every other mention across all `.lean` is prose,
plus one `#print axioms` target. `fOdd_decreasing` and `fOdd_tendsto_half`
still assume `OddNumericalFacts` and use `hnum.remainder`.

Three things stand between the two, and only the first is analysis:

1. five analytic side conditions threaded unproved through the file --
   `hsum1`, `hsum`, `hmul3`, `hcd1`, `hcd2`;
2. the certified numerics `hCN`, `hNEARU`, `hsplitD`, `hMR`, which are fields
   of the other three structures -- so wiring it in would **relocate** the
   trusted base, not shrink it. The honest count of assumptions about the world
   does not drop;
3. the `hk : 1 <= k` binder (see above).

So "derive `remainder` in Lean" is not one open problem, and the gain from (1)
alone is presentational. Do not report it as derived because the theorem exists.

## Before committing changes to `paper/`

Compile twice and confirm a clean build:

    pdflatex -interaction=nonstopmode proof.tex   # x2, for cross-references

Zero `^!` errors and zero "undefined" warnings on the second pass. Regenerate
`paper/proof.pdf` and commit it alongside the `.tex`.

A clean build is not the same as a submittable paper — the AI-disclosure
placeholder compiled into a clean 21-page PDF with zero errors and zero
undefined references, so every signal the repo had said the paper was fine.
Run the gate too:

    python3 paper/check_ready.py

It fails while any submission blocker is present (unfinished markers in the
body, a placeholder AI disclosure, a stale `proof.pdf`, or the `k >= 59`
remainder range disagreeing across the three places) and prints the blockers
only the author can clear.

## Numerics

`pip install python-flint` (needs `--break-system-packages` on this image).
Scripts are rerunnable and each has its settings of record in the docstring;
logs sit beside them. Prefer handing over a script plus the exact run command
to running long jobs inline.

Two recurring traps:

- **arb prints lossily.** `str(arb)` rounds the midpoint and inflates the
  radius to compensate, so a perfectly tight ball can display as `[+/- 0.69]`.
  Read `.lower()` / `.upper()` / `.rad()` before concluding anything is wrong.
- **Check the consuming script before inferring what a number means.** Most
  false alarms in this repo have come from reading a magnitude and guessing
  its semantics instead of reading the code that uses it.

## Lean

**Nothing Lean has been validated.** Three routes were checked on 2026-10-22
and all three are closed:

- *Locally* — the toolchain downloads (the `v4.33.0-rc1` GitHub release asset
  returns 302), but **both Mathlib cache hosts are unreachable**
  (`mathlib4.lean-cache.cloud` and `lakecache.blob.core.windows.net`), so
  `lake exe cache get` cannot work and Mathlib would have to be built from
  source on 2 cores / 7 GB. Not viable.
- *CI* — runs are accepted and then get **no runner**: `runner=NONE`,
  `steps=0`, reported as `conclusion: failure` exactly like a build error. See
  the comment block at the top of `.github/workflows/lean.yml` for the
  one-command check that tells the two apart.
- *Billing* — the quota endpoints are not reachable from a repository-scoped
  session, so the cap has to be read from the GitHub UI.

Until a run comes back with `steps > 0`, Section 8 and Table 1 of the paper
describe a state no build has confirmed, and `paper/check_ready.py` says so.

`lake build`; `#print axioms` targets are in `odd-proof/axcheck.lean`. The
`*NumericalFacts` structures are assumed hypotheses with no instance — that is
the trusted computing base, deliberately (manuscript Caveat 1.3b). There must
be no `sorry` anywhere.
