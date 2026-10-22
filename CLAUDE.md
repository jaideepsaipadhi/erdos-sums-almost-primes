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
