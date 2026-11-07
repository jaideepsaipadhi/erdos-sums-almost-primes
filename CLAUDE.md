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

### Two constants had NO generating artifact, and one of them was stated wrong

Repaired 2026-11-05. `101.245` and `1.45` existed only as hardcoded literals
(`k0_end_to_end.py`, `measure_impact.py`, `check_paper_phi.py`,
`k1_far_range.py`), annotated "certified separately", with
`check_paper_phi.py` reading them back out of the manuscript -- so paper and
scripts agreed only because each had been copied from the other. Writing the
artifacts found a real error in one of them.

**`101.245` bounds the POLE-FREE part, not the regularized product.** On
`|z| = 4.2`, with `rho = 0.1749324` the residue at `z = 3`:

    sup |G_2(1,z) - rho/(3-z)|  =  95.49   <= 101.245   <- what the SCRIPTS use
    sup |(1 - z/3) G_2(1,z)|    = 228.94    > 101.245   <- what the PAPER said

The scripts' tail envelope `T(i) = rho/3^(i+1) + supH/4.2^i` is residue plus
Cauchy on the pole-free remainder, and is correct with 5.7% to spare, so
`U_max`, `V_max` and `S*` were never in doubt. The manuscript's
`eq:contour-certified` named `(1-z/3)G_2` and then derived
`|c_i| <= 354.36 3^-i` from it -- a false premise. Corrected derivation gives
`|c_i| <= 101.31 3^-i`, 3.5x SHARPER, so `354.36` survives a fortiori and is
kept as the stated constant. **Do not "simplify" eq:contour-certified back to
the regularized product**; `numerics/contour_certified.py` (log `contour.log`)
certifies both suprema and cross-checks `rho` against the hardcoded literal.
If `U_max` or `V_max` ever has to be re-derived, note the sensitivity: feeding
`supH = 226.1` into `T(i)` gives a `U` tail of `0.1076`, already above the
stated `U_max = 0.08436`. The margin lives entirely in using the right
function.

**`1.45` is elementary and enormously loose.** `T_k = f_k - I_k` unfolds to
`sum_{Omega(n)=k} n^-2/log n`, all terms positive, so with `n >= 2^k` and
Cauchy at `|z| = 3` on `F(2,.)`:

    2^k |T_k| <= M(3)/(k log 2) (2/3)^k,   M(3) = prod_p (1-3p^-2)^-1 <= 7.96896

which beats `1.45/k` from `k >= 6` and at `k = 900` by `10^158`.
`numerics/tk_certified.py`, log `tk.log`. Consequence: **the threshold 900 is
inherited from `eq:full-sweep-ranges`, not forced by `T_k`** -- the paper used
to say it came "from `T_k` alone", which is false. The repository's other
`1.45` (`certified.py`'s `DELTA`, the quadrature ellipse semi-minor axis) is
an unrelated coincidence; don't treat it as the source.

### The appendix was stale by one run

The committed certificate is `KMAX = 500` (`u_+ = 1750`, 2194 panels, largest
radius `4.539e-87`, at `k = 2`). The appendix described a superseded
`KMAX = 199` run and quoted `1.1e-87` -- a figure no committed artifact
contains -- with the "twenty orders of magnitude" gap belonging to it. Now
stated for the run of record (tails `10^-272` and `10^-24618`, radius
`4.6e-87`, gap 185 orders), and `check_proof_spine.py` reads both out of
`certificate.json`. Only `6 <= k <= 199` of the run is used.

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

### The odd sweep now certifies from k=1, and its chunks are committed

Regenerated 2026-11-05. `fodd_combine.py` added tail terms only from `k = 2`
and compared only adjacent pairs from `k = 2`, so the committed log said
`[2,75]` while the manuscript claimed `1 <= k <= 75`. Both loops now start at
1. The rerun (335 panels, two halves, ~50 min on 2 cores at PREC=1000)
reproduces **every enclosure identically** -- no midpoint moved, no radius
widened -- and now certifies `[1,74]`.

**The verdict range is `[1, KMAX-1]`, not `[1, KMAX]`**: the loop compares
pairs `(k, k+1)`, so `KMAX = 75` reaches `k = 74`; the pair `(75,76)` would
need `g_76`. The enclosure range is `[1,75]`. The paper now states the two
separately, and the overlap with the analytic `k >= 59` range is therefore
**sixteen** indices (59..74), not seventeen. `check_proof_spine.py` checks the
log's verdict line against the paper's claim, and that a `k = 1` row exists.

`ochunks/*.txt` are now committed (44K, with a `.gitignore` negation), because
without them `fodd_combine.py` cannot be run at all and the hour-long sweep
would have to be redone to re-derive the verdict.

## The committed certificates, and what actually backs each sweep range

`numerics/verify.py` must be **run from `numerics/bm-rebuild-v21/`** — its
docstring says so, and from anywhere else it silently skips the criterion
sweeps (`load()` returns `None` and the loop `continue`s) while two unrelated
checks error out. Run correctly it passes all 17. Don't report it as broken
without checking the directory first.

What backs `eq:full-sweep-ranges`, regenerated 2026-11-05:

| artifact | what it holds | range | script |
|---|---|---|---|
| `numerics/certificate.json` | `f_k` enclosures, compared pairwise | `k = 2..500` | `certificate.py` |
| `bm-rebuild-v21/crit_78_734.json` | refined criterion `> 0` (min 0.91) | `78..734` | `crit_refined.py 78 734` |
| `bm-rebuild-v21/crit_650_899.json` | fallback criterion `> 0` from 728 (min 27.65) | `728..899` | `crit_fallback.py 650 899 crit_650_899.json` |
| `bm-rebuild-v21/crit_900_2439.json` | fallback criterion `> 0` (min 10115.96) | `900..2439` | `sweep_900_2439.py` |

The blocks now **overlap**: `[78,734] [728,899] [900,2439]`. They used to abut
exactly at 735 with no slack, and `verify.py` checked only the zero crossing of
the file carrying that slice, so a one-off change could have opened a silent
gap. `verify.py` now checks the union for gaps directly.

### Both fallback certificates were regenerated; the old ones had the wrong provenance

**This section used to claim `crit_78_734.json` and `crit_certified.json` have
"no generating script in the repository". That was wrong both ways.**
`crit_refined.py` takes `klo khi outfile` and generates the first — with its run
of record committed beside it as `sweep_78_734.log`. Confirmed 2026-11-05:

    python3 crit_refined.py 78 734 out.json     # ~6 min

reproduces `crit_78_734.json` **byte-identical**, 657 of 657 values, and
reprints the log of record (`0 non-positive`, `k=78: 0.91`,
`k=734: 33754.05`). So the refined certificate was never the problem, and
`K0 = 78` rests on a sweep that reproduces exactly — worth knowing, because its
margin is `0.91` against values reaching `33754`, and it is the only sweep where
a drift in the inputs could move `K0`.

The two *fallback*
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
itself**, since GLW's `a_1 = d log2/4` is exactly `H_o(1,2) log2/4`.

**Read the next subsection before using any of this.** The paragraph above is
how the reduction was first found, and it is superseded: the `s`-derivative
possibility is now ruled out outright rather than argued around, and what
remains is one asymptotic with no primes in it.

### The boundary half of Section 7 is OUT of the manuscript (2026-11-07)

Decision of record. The paper now carries only the **interior** case:
Conjecture 7.1, the hypothesis discussion, the singularity structure,
`eq:HP-def`, Proposition 7.2, Corollary 7.3, and the `genP_check.py`
calibration. Everything on `q = 2` -- `eq:boundary-pole`,
`eq:boundary-ratio`, `eq:GLW-value`, `eq:boundary-predicted`, the fitting
table, and all of the former \S7.3 (`eq:boundary-exact`, `eq:Im-def`,
`eq:boundary-reduction`, `eq:freeze-error`, `eq:boundary-consequence`,
`eq:boundary-final`, `eq:Im-asymptotic`) -- was removed, and the section now
closes with a short paragraph saying the boundary case is open and will be
treated separately.

**Why:** 35 pp -> 31 pp, and it was the only unproved material in the paper.
Prop 7.2 + Cor 7.3 are proved outright; the boundary reduction rested on TWO
unproved ingredients (`eq:Im-asymptotic` and `eq:freeze-error`), so a referee
would have weighed them against Theorems 1.1 and 1.2, which do not depend on
Section 7 at all. Verified before cutting: the dependency is one-directional.
Section 7 cites 14 labels from \S\S1--3; the rest of the paper referenced
Section 7 in exactly 5 places, all `\ref`s in the introduction's roadmap, plus
two abstract sentences. Nothing in \S\S2--6, \S8 or the appendix touched it.

**All the mathematics is kept in this repository** for the separate note:
`Im_check.py`/`Im.log`, `km_check.py`/`km.log`,
`boundary_freeze_check.py`/`freeze.log`, `boundary_check.py`/`boundary.log`,
and every finding recorded in the sections below. Do not delete them, and do
not re-derive them: the sections below are the state of that work, including
the two corrections (`I_0` diverges; the freezing costs `Theta(k 2^-k)`, not
`O(e^-k)`) and the expanding-circles repair.

`check_proof_spine.py`'s `K_m` guard is now conditional: it fires if the
manuscript quotes the figures and the log is missing, and reports `n/a` if the
manuscript does not quote them. That asymmetry is deliberate -- contrast the
five round-up checks, where a missing LOG is a hard failure because the
paper's numeral is present and unbacked.

### The `s`-derivatives are GONE, and point two is now ONE primes-free asymptotic

Superseded 2026-11-05. The earlier framing — "if the coefficient is
`A Phi + B d_s Phi`, cancellation needs one exact `kappa`" — is no longer the
right statement, because **no `B` can occur at all.** The route is an exact
identity. Expanding the pole of `H_P = Phi_P/(1 - z 2^-s)` in powers of `z`,

    P_k^P(s) = sum_i phi_i(s) 2^{-(k-i)s} sum_{j<=k-i} (2^s log zeta(s))^j/j!,
    phi_i = [z^i] Phi_P,      Phi_P = H_{P \ {2}}.                      (*)

(*) is exact for `s > 1`, not asymptotic; at `k = 1` it collapses to
`sum_{p in P} p^-s` — the RESTRICTED sum, not `sum_p p^-s` — the `log zeta`
terms cancelling against `phi_1`. **Verified to 1e-17 against direct Dirichlet
sums over `n <= 3e6` at `s = 4`, `k <= 3`, for `P` = all primes, minus `{3}`,
minus `{3,5}`** (`Im_check.py --identity`).

Integrate `ds` over `[1,inf)` and freeze `phi_i` at `s = 1`. What remains
carries no primes:

    I_m = int_1^inf 2^{-ms} sum_{j<=m} (2^s log zeta(s))^j/j! ds
        = (1/m!) int_1^inf int_0^inf (log zeta(s) + 2^-s v)^m e^-v dv ds,

    f_k^P = sum_{m=1}^{k} phi_{k-m}(1) I_m + int_1^inf phi_k(s) ds + O(k 2^-k).

Two things here were wrong in the first write-up and are load-bearing:

- **`I_0 = int_1^inf 1 ds` DIVERGES**, so the `m = 0` term must be kept
  unfrozen; `int phi_k(s) ds = O(R^-k/k)` for any `R < 3` by Cauchy.
- **The freezing does NOT cost `O(e^-k)`.** The mass sits at `s - 1 ~ e^-k`,
  but the Jensen error is governed by the first moment
  `K_m = int (s-1) [I_m integrand] ds`, which is `Theta(m 2^-m)`:
  `K_m 2^m/m` = 0.381/0.397/0.411/0.416 at `m = 16/24/32/36`, against
  `e^-m/K_m = 1.1e-6` at `m = 36`. So the error is `sum_i phi_i'(1) K_{k-i}
  = O(k 2^-k)`, and **the reduction is accurate to `o(k^2 2^-k)`, not
  `o(2^-k)`.**

If `I_m = c0 + A m^2 2^-m + o(.)` then summing against `phi_{k-m}(1)` and
against `phi_{k-m}(1) 2^{k-m} m^2` gives, immediately,

    f_k^P -> c0 * Phi_P(1,1),     [k^2 2^-k] f_k^P = A * Phi_P(1,2).

**Both depend on the numerator only through its VALUE** — but the honest claim
is only that no `d_s Phi` term enters the `k^2 2^-k` COEFFICIENT. One does
enter, via the freezing error, at order `k 2^-k`. That order is irrelevant to
Conjecture 7.1, whose sign is decided by `k^2 2^-k`, which is why `B = 0`
still does the work; do not state it unqualified.

`I_m` has no primes in it, so its two constants are pinned by the single case
`Q` empty, where both answers are known:

    Lichtman f_k -> 1,  Phi(1,1) = H_o(1,1) = 1/2   =>   c0 = 2
    GLW a_1 = d log2/4, Phi(1,2) = H_o(1,2) = d     =>   A  = -log2/4

which gives, for every admissible `P` with `q = 2`,

    f_k^P -> prod_{p in Q}(1 - 1/p),
    [k^2 2^-k] f_k^P = -(log2/4) d prod_{p in Q}(1 - 2/p)  <  0.

That also **derives the centring constant** the boundary numerics use, which
the earlier text had to assume by analogy. And since `C < 0` gives
`f_{k+1} - f_k = C 2^-k (1+2k-k^2)/2 + o(.)` with the bracket negative for
`k >= 3`, the sequence eventually INCREASES — the half of Conjecture 7.1 that
Corollary 7.3 does not supply.

**So exactly one statement remains, and it mentions no primes:**

    I_m = 2 - (log2/4) m^2 2^-m + o(m^2 2^-m).

Not proved. The obstacle is concrete: `J = -zeta/zeta'` is NOT integrable at
`u = 0` (`int_0 J du = int^inf ds = inf`), so the naive bound on the inner
integral fails and the `v`-integral's convergence is marginal — which is
exactly where the `m^2` comes from. Don't retry the crude route: bounding
`J <= C e^-u` globally is false, and the formal term-by-term expansion of `J`
produces a spurious `(e^{2/3}/3)^m = 0.649^m` term that beats `2^-m`, which is
the signal that the interchange is invalid, not a result.

Numerically unambiguous, though: `I_m` for `8 <= m <= 36` gives `I_m -> 2` to
`3e-9`, and `(I_m-2)/(m^2 2^-m)` DECREASES monotonically `-0.0875 -> -0.1194`
(its magnitude rising), extrapolating to `-0.17379 / -0.17301 / -0.17277`
across three windows in the `A + b log m/m + c/m` basis — within `0.3%` of
`-log2/4 = -0.17329`. The one tabulated basis omitting `log m/m`
(`1/m + 1/m^2`) lands `8.0%` off and the two-parameter `log m/m` fit `8.6%`,
so that correction is doing real work — but this is **not** independent
corroboration of GLW's `O(k log(k+1))`: the basis was chosen with that
remainder in mind. Don't upgrade it.
`numerics/Im_check.py`, log in `Im.log`; mpmath, no certificate.

### The unfrozen m=0 term needs EXPANDING circles, not fixed ones

Found by referee 2026-11-05. The step disposing of the divergent `m = 0` term
used to read "Cauchy on `|z| = R^s` with `R < 3` gives
`|phi_k(s)| <= M R^-ks` uniformly in `s`, by Proposition 7.2(ii)". **No such
uniform `M` exists.** The complement of `P \ {2}` contains 2, contributing
`(1-2^-s)^z`, and at `z = -R^s` that factor has modulus
`exp(R^s log(1-2^-s)^-1) ~ exp((R/2)^s)`, unbounded for `R > 2`. Measured for
`P` = all primes, `R = 2.5`: `log|Phi|` at `z = -R^s` runs
`2.50, 2.61, 6.00, 14.56, 35.53, 86.74` at `s = 1,4,8,12,16,20`.

The repair is the circles `|z| = R 2^{s-1}`, on which `|z| 2^-s = R/2` is
CONSTANT and `|z| p^-s <= (R/2)(2/3)^s` for `p >= 3`. Then
`M_R = sup_s sup_{|z|=R2^{s-1}} |Phi_P| < infty` (measured: `log|Phi|`
decreases monotonically to exactly `R/2 = 1.25`), and
`|phi_k(s)| <= M_R R^-k 2^-k(s-1)`, so the integral is
`<= M_R R^-k/(k log 2)`. Note this uses 7.2(i)'s ESTIMATE, not 7.2(ii)'s
fixed-circle conclusion -- don't cite (ii) here.

Two related corrections in the same paragraph: the `i`-tails are `O_R(R^-k)`
and `O_R((2/R)^k)` for each fixed `R < 3`, not `O(3^-k)` and `O((2/3)^k)`
(7.2(ii) forbids `R = 3`); and `E_k = Theta(k 2^-k)` holds iff
`d_s Phi_P(1,2) != 0`, NOT iff `phi_1'(1) != 0` -- no single `i` dominates,
every `i` contributes at that order.

### Section 7's convergence aside was false as written

"The product converges locally uniformly for ANY set of primes, since
`sum_p p^-sigma < infty` for `sigma > 1/2`" is true only of the `prod_{p in P}
L_p` factor. The complement factor `prod_{p in Q}(1-p^-s)^z` has logarithm
`~ -z p^-s` and needs `sum_{p in Q} p^-sigma < infty`, i.e. `sigma > 1` --
and `s = 1` is where every constant in the section is evaluated. It
contradicted both the preceding paragraph and 7.2(i)'s own proof.

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
H_o(1,2))`, which carries both. That contrast was the first reason to think the
form is structural; the exact identity in "the `s`-derivatives are GONE" above
then settled it, so `B = 0` is established and not merely expected. The general
coefficient is `a_1 prod_{p in Q}(1 - 2/p) > 0`.

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
