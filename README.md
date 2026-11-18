# Monotonicity of Erdős sums

Certified computations for *Monotonicity of Erdős sums* (Jaideep Sai Padhi),
together with a Lean 4 formalization of the analytic reduction.

Write $f_k=\sum_{\Omega(n)=k}1/(n\log n)$, and let $g_k$ be the same sum over
odd $n$. The Banks–Martin conjecture was disproved, and the global minimum
located at $k=6$, in Lichtman's *Almost primes and the Banks–Martin
conjecture* (arXiv:1909.00804). The paper proves that the increase is strict
at every step from $k=6$ onward — a minimum at $6$ does not by itself give
$f_k<f_{k+1}$ for all $k\geq6$ — and that $g_k>g_{k+1}$ for every $k\geq1$,
which is the case $\mathcal{Q}=\{2\}$ of a general statement proved in the
paper's Section 7.

## What in here backs the paper, and what does not

**This is the distinction to read first.** The paper's certified propositions
rest on the Arb/FLINT computations in `numerics/` and
`odd-proof/numerics/` — those, their logs and the certificate are what
Section 8 of the paper cites.

**The Lean development in `Banksmartin/` and `Odd/` is not cited by the
paper, and a passing build of it would not establish the paper's theorems.**
Earlier versions of the manuscript described the development, and earlier
versions of this file claimed specific theorems were machine-checked with a
given axiom set. Those claims were never verified in any environment
available here: both Mathlib cache hosts are unreachable, so
`lake exe cache get` cannot run, and CI accepts runs and then assigns no
runner, which is reported identically to a build failure.
`.github/workflows/lean.yml` documents the one-command check that
distinguishes a missing runner from a build error.

A third-party service, [Paperlane](https://github.com/pragyaangaur/Paperlane),
reports that the development compiles with no `sorry` at commit
`18654533cb27` under `leanprover/lean4:v4.33.0-rc1`, with axioms **not**
checked. Taken at face value that establishes one thing: the files typecheck
at that commit. It is not a verification of the mathematics, for two
reasons that are worth stating plainly.

First, the `NumericalFacts`, `NumericalFactsFull` and `OddNumericalFacts`
structures are assumed hypotheses, and **no instance of any of them is ever
constructed**. Every theorem resting on them is therefore an implication from
certified numerics, not an unconditional result. That is deliberate — it is
the trusted computing base — but it means a green build says nothing about
whether those hypotheses hold.

Second, and more sharply: a field of such a structure can be *unsatisfiable*
without any build noticing. `NumericalFactsFull.Eexp_bound` was in exactly
that state until its quantifier was bounded, which would have made the
theorems depending on it vacuous rather than false. Vacuous theorems compile
cleanly and carry no `sorry`. That defect was found by reading the statement,
not by running `lake build`, and no build check of any kind would have caught
it.

So the build report is welcome information and is recorded here, but nothing
in this repository should be read as a machine-checked claim about the
results in the paper. For the same reason no build badge is displayed: a
green check would assert something neither that run nor any run of its kind
can support.

## Reproducing the certified numbers

Needs `python-flint` (`pip install python-flint`, with
`--break-system-packages` on some images).

    cd numerics/bm-rebuild-v21 && python3 ../verify.py

`verify.py` **must** be run from that directory; from anywhere else it
silently skips the criterion sweeps. Run correctly it checks all 17 items:
the sweep tables, the $\Gamma$ data, the union of the criterion ranges for
gaps, and the certificate's SHA-256.

Four more guards check the manuscript against the certificates rather than
against itself, which is the failure mode that produced most of the errors
this project has found:

    python3 numerics/check_proof_spine.py      # every printed numeral vs its log
    python3 numerics/check_paper_phi.py        # the criterion at the threshold
    python3 numerics/odd_beta_certified.py     # beta > 0 and the k = 59 base case
    python3 paper/check_ready.py               # submission blockers

`numerics/check_lean_constants.py` compares the Lean numerals with the
certificates. It is retained for the development's own sake; the paper does
not depend on it.

Each script carries its settings of record in its docstring, and the log of
that run sits beside it.

## Two traps worth knowing before reading any log

- **Arb prints lossily.** `str(arb)` rounds the midpoint and inflates the
  radius to cover the rounding, so a tight ball can display as though it were
  wide. Read `.lower()`, `.upper()` and `.rad()`. A monotonicity check in
  `odd-proof/numerics/fodd75.log` appeared to fail for $k\geq65$ for exactly
  this reason; the true radii are twenty orders of magnitude smaller than the
  printed ones.
- **Check the consuming script before inferring what a number means.** The
  constant $101.245$ bounds the pole-free part $G_2(1,z)-\rho/(3-z)$, not the
  regularized product $(1-z/3)G_2(1,z)$, whose supremum on $|z|=4.2$ is about
  $228.95$. The manuscript named the wrong one of the two for several drafts.

## Layout

    paper/proof.tex              the manuscript (28 pp)
    paper/check_ready.py         submission gate
    numerics/                    certified computations, unrestricted case
    numerics/bm-rebuild-v21/     criterion sweeps and verify.py's working dir
    odd-proof/PROOF.md           the odd argument
    odd-proof/numerics/          certified computations, odd case
    Banksmartin/, Odd/           the Lean development (see the caveat above)
    TRUSTED-BASE.md              audit of the Lean structures' fields

## Acknowledgement

Jared Duker Lichtman provided guidance throughout this work.
