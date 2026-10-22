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
| `C_N ≤ 367.8435` in the near range | `34.14` for `k ≥ 59` (`nearabs.log`) | one constant serves both the signed and the absolute sum; keeps `MR ≤ 4900` and the ledger unchanged |

The margin at `k = 2433` was 139 before the three numeral corrections to
`lem:phi-base`; `check_paper_phi.py` now recomputes it from the certified
constants and reads it out of the manuscript, so the two cannot drift again.

## Before committing changes to `paper/`

Compile twice and confirm a clean build:

    pdflatex -interaction=nonstopmode proof.tex   # x2, for cross-references

Zero `^!` errors and zero "undefined" warnings on the second pass. Regenerate
`paper/proof.pdf` and commit it alongside the `.tex`.

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

`lake build`; `#print axioms` targets are in `odd-proof/axcheck.lean`. The
`*NumericalFacts` structures are assumed hypotheses with no instance — that is
the trusted computing base, deliberately (manuscript Caveat 1.3b). There must
be no `sorry` anywhere.
