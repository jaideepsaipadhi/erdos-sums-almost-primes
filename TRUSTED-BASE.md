# The trusted base: what is assumed, and what need not be

`NumericalFacts`, `NumericalFactsFull` and `OddNumericalFacts` are `Prop`
structures with no instance.  That is deliberate (manuscript Caveat 1.3b): Lean
proves the reduction, the Arb certificates supply the numbers, and the two meet
at these structures.  This note is an audit of what is actually in there, since
"the trusted base" is otherwise a phrase rather than a list.

The question asked of every field is narrow: **is this a fact about an
analytic object, or a fact about an explicit formula?**  The first kind cannot
leave the trusted base without a verified interval-arithmetic layer in Lean.
The second kind is a lemma that happens to have been assumed, and can leave
today.

## The count

| structure | fields |
|---|---|
| `NumericalFacts` | 11 |
| `NumericalFactsFull` | 19 |
| `OddNumericalFacts` | 6 |

The two unrestricted structures overlap heavily; `NumericalFactsFull` is the
primitive one, from which `erdos_sums_increase_from_six'` derives the far range
rather than assuming it.

## Tier A — not numerical facts at all (one of two now proved)

Two fields of `NumericalFactsFull` (and the same two of `NumericalFacts`)
quantify over an **explicit elementary formula** and nothing else:

    DBound m  = log 2 * m * log (m+1) + 1
    RBound k  = (log 2 / 4) ((2k-2) Umax + 2 Vmax + 4 Umax)
                + Sstar (2 DBound k + DBound (k+1))
                + alph (3k + 4)
                + 3 (1.45/k + 1e-3)
    phiBound k = aa (k^2 - 2k - 1) - RBound k

* `phi_mono : forall m >= 2440, phiBound m <= phiBound (m+1)`
* `phi_at_k1 : 0 < phiBound 2440`

Neither mentions a prime, a contour or a limit.  `phi_mono` is the statement
that a quadratic eventually outruns a linear-plus-log, and the difference is

    phi(k+1) - phi(k) = aa (2k - 1)
                        - (log 2 / 2) Umax
                        - Sstar (2 (DBound(k+1) - DBound k) + (DBound(k+2) - DBound(k+1)))
                        - 3 alph
                        + 3 * 1.45 (1/k - 1/(k+1))

with the last term positive.  Everything needed to sign this is already in the
structure except one scalar:

* `aa = aOneConst = dConst * log 2 / 4` is bounded below by `d_enclosure`;
* `Sstar <= 6.9763` by `Sstar_bound`;
* `alph <= 15.4257` by `alpha_bound`;
* `DBound` is monotone (`DBound_mono`, already proved) and its increments are
  `O(log k)`, bounded explicitly from the formula;
* `log 2` has a Mathlib enclosure (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`);
* **`Umax` has no upper bound anywhere in the structure.**

Note that `Vmax` enters `RBound` only as `+ 2 Vmax`, constant in `k`, so it
cancels in the difference: `phi_mono` does not need it at all.  It is needed
for `phi_at_k1`, which is a single evaluation.

**DONE.**  `phi_mono` is now proved (`phiBound_mono_of_bounds`) and gone from
both structures, which instead carry `U_bound : Umax <= 0.08436` and the three
nonnegativity facts the proof needs.  What follows is the reasoning that led
there, kept because `phi_at_k1` is the same shape.

**The proposal was.**  Add one field

    U_bound : Umax <= <the value k1_far_range.py already certifies>
    V_bound : Vmax <= <likewise>          -- needed only for phi_at_k1

and prove `phi_mono` and `phi_at_k1` as theorems.  Net effect on the trusted
base: two universally quantified assumptions, which no finite computation can
ever discharge and which a reader cannot check by inspection, are replaced by
two scalar bounds that the numerics already produce and that `verify.py` can
check.  That is a strictly better trade even though the field count barely
moves -- a `forall` is a much larger thing to be asked to believe than a
number.

## Tier B — a Mathlib gap, and it is stated 1200x tighter than it needs to be

* `OddNumericalFacts.gamma_gt : 0.5772156 < eulerMascheroniConstant`

Mathlib does have a lower bound, just a weak one
(`Real.one_half_lt_eulerMascheroniConstant`), alongside
`eulerMascheroniConstant_lt_two_thirds`.  The usable route is

    Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
      : harmonic n - log (n+1) < gamma

whose gap to `gamma` is about `1/(2n)`.  So the cost of proving a lower bound
is set entirely by how tight that bound is -- and this one is far tighter than
the argument needs.

`gamma_gt` is used once, to get `0.1556 <= betaOdd` where
`betaOdd = d (log 2 - Sodd + gamma)`.  Taking `d` and `Sodd` at the worst ends
of their own certified enclosures (`d >= 0.3786950 - 5.3e-8`,
`Sodd <= 0.8593953 + 3.3e-6`), what the argument actually requires is

    gamma >= 0.5771362259        (true gamma is 0.5772156649, margin 7.9e-5)

against the stated `0.5772156`, whose margin is `6.5e-8`.  Through the
Mathlib route that is the difference between

    as stated:   error < 6.5e-8   ->  harmonic n for n > 7,703,978
    as required: error < 7.9e-5   ->  harmonic n for n > 6,294

`harmonic 7.7e6` is not going to evaluate in the kernel; `harmonic 6300` is a
rational with a few thousand digits, which is heavy but not absurd.  So the
first move on this field is not to prove it -- it is to **weaken it to what
the proof uses**, which costs nothing, is in the safe direction (a weaker
hypothesis is a stronger theorem), and is a Lean-only change: `0.5772156`
appears nowhere in the paper or in `PROOF.md`.

One caution before doing it.  Weakening the constant shrinks the margin in the
downstream `0.1556 <= betaOdd` step from `7.9e-5` to a few parts in `1e-6`.
The inequality stays strictly true, but the tactic that discharges it may need
more help, so the two changes belong in one CI iteration rather than being
assumed independent.

## Tier C — irreducible without verified interval arithmetic

Everything else, in three kinds.

**Infinite products and sums over primes.**  `d_enclosure`, `d_enc`,
`rho_enclosure`, `Sodd_enclosure`.  `dConst` is a `tprod` over `Nat.Primes`;
`Sodd` a `tsum` over primes `>= 3`.  Discharging these in Lean means proving
convergence rates and summing rigorously in the kernel.

**Contour suprema and derivative bounds.**  `Sstar_bound`, `alpha_bound`,
`Gamma_bound`, `MR_bound`, `M0_bound`, `g_deriv`, `g_deriv_bound`,
`alpha_dom`, `Sstar_dom`.  These are the Arb sweeps.  `M0_bound` quantifies
over every `theta` and every `u > 1`.

**The Cauchy estimate itself.**  `OddNumericalFacts.remainder` and
`NumericalFacts.source_bound` / `UV_bound` / `Eexp_bound`.  This is the
analytic heart, not a number: it is where complex analysis enters.

**The finite sweeps.**  `sweep_low` (6..199), `sweep_mid` (78..899),
`sweep_high` (900..2439), and the odd `sweep_low` (1..58).  These are finite --
2,490 and 58 instances -- so they are *in principle* decidable, but each
instance needs `f k` to enough precision, and `f` is not kernel-computable.
They would be the last thing to fall, not the first.

## The constraint that shapes all of this

There is no Lean toolchain in the working container, and none can be installed
from it: `elan.lean-lang.org` and the GitHub release are both refused by the
egress allowlist, and Mathlib's olean cache host is unreachable.  **CI is the
only compiler this project has from here**, at roughly ten minutes per
iteration.

That argues against developing anything large blind.  It argues *for* Tier A,
which is two small lemmas over explicit formulas where the proof obligations
are ordinary real arithmetic (`nlinarith` with a `log 2` enclosure and the
existing `DBound_mono`), and where a failed iteration tells you something
specific.

## Recommendation

Hold Caveat 1.3b as the stated position -- Tier C is not going anywhere
without a verified interval layer, and claiming otherwise would be dishonest
about what is machine-checked.  But Tier A should not be inside the caveat at
all: it is there by convenience, not by necessity, and two `forall`-statements
about a quadratic are the weakest things in the base to be asking a reader to
take on trust.
