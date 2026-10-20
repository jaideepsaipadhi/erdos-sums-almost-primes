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

| structure | fields | was |
|---|---|---|
| `NumericalFacts` | 14 | 11 |
| `NumericalFactsFull` | 22 | 19 |
| `OddNumericalFacts` | 4 | 6 |

The unrestricted counts went **up** by three while the base got smaller, and
the table is the wrong way to read this.  Five things left: `phi_mono`,
`phi_at_k1` and `d_enclosure` on the unrestricted side, `gamma_gt` and `d_enc`
on the odd side -- every one of them now a theorem.  Six scalars arrived
(`U_bound`, `V_bound`, four nonnegativity facts) to support the Tier A proofs,
and those six are **bounds on abstract variables**, which assert nothing about
the world: they fix a numeral.  So the trade was two unfalsifiable
`forall`-statements and three facts about infinite products, for six numerals.
`OddNumericalFacts` went 6 -> 4 and gained nothing at all.

Counted from the structure bodies with docstrings stripped -- counting them in
is how `recomputed`, a word in a comment, briefly became a sixteenth field.

The two unrestricted structures overlap heavily; `NumericalFactsFull` is the
primitive one, from which `erdos_sums_increase_from_six'` derives the far range
rather than assuming it.

## Tier A — not numerical facts at all (both now proved, both gone)

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

**DONE, both of them.**  `phi_mono` is proved as `phiBound_mono_of_bounds`
and `phi_at_k1` as `phiBound_pos_at_2440`; neither is a field of either
structure any more.  In their place the structures carry five scalars --
`U_bound : Umax <= 0.08436`, `V_bound : Vmax <= 1.90747`, and the three
nonnegativity facts `Umax_nonneg`, `Vmax_nonneg`, `Sstar_nonneg`,
`alph_nonneg` -- every one of which the Arb sweeps already produce and
`verify.py` can check.  Tier A is empty.  What follows is the reasoning that
led there, kept because it is the argument the two proofs follow.

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

`harmonic 7.7e6` is not going to evaluate in the kernel; `harmonic 7614` is a
rational with a few thousand digits, which is heavy but not absurd.  **DONE:**
the field was first weakened to `0.57715 < gamma`, which leaves `betaOdd` a
margin of `5.2e-6` and needs `n > 7614` in place of `n > 7703978`, and is now
proved outright as `Odd.gamma_lower_bound`, at `n = 8191` so that
`log 8192 = 13 log 2` closes the logarithm against Mathlib's enclosure rather
than needing its own.  `gamma_gt` is removed from `OddNumericalFacts`.  The reasoning was that the first move on this field is not to
prove it -- it is to weaken it to what the proof uses, which costs nothing, is in the safe direction (a weaker
hypothesis is a stronger theorem), and is a Lean-only change: `0.5772156`
appears nowhere in the paper or in `PROOF.md`.

One caution before doing it.  Weakening the constant shrinks the margin in the
downstream `0.1556 <= betaOdd` step from `7.9e-5` to a few parts in `1e-6`.
The inequality stays strictly true, but the tactic that discharges it may need
more help, so the two changes belong in one CI iteration rather than being
assumed independent.

## Nine fields are not assumptions at all

Before Tier C, a correction to how this document counted.  `Sstar`, `alph`,
`Gam`, `Umax`, `Vmax`, `M0` and `MR` are **arguments** of the theorems:

    theorem erdos_sums_increase_from_six (Sstar alph Gam Umax Vmax : ℝ)
        (hnum : NumericalFacts Sstar alph Gam Umax Vmax) : ...

They are abstract reals, not defined objects.  So `Sstar_bound : Sstar <=
6.9764`, `alpha_bound`, `Gamma_bound`, `MR_bound` and the five nonnegativity
facts do not assert anything about the world -- they fix the numeral attached
to a bound variable, and **no proof of them is possible or needed.**  The real
content is in the fields that COUPLE those symbols to defined objects:
`source_bound` (to `E`) and `remainder` (to `fOdd`).  Those are the Cauchy
estimate, and they are Tier C proper.

Counting those nine as debt overstated the trusted base.  The honest count of
assumptions about the world is six: `rho_enclosure`, `Sodd_enclosure`,
`source_bound`, `remainder`, and the four sweeps.

## Which fields are load-bearing, by actual use

Counted by searching the development for each field's projection.  Two fields
have NO consumer, and seven more constrain abstract variables, so the honest
count of assumptions about the world is well under the field count.

| field | consumers | status |
|---|---|---|
| `rho_enclosure` | 0 | **proved and removed** (`rhoConst_upper_bound`) |
| `Gamma_bound` | 0 | vacuous; kept as the paper's mirror, documented at the field |
| `Sstar_bound`, `alpha_bound`, `MR_bound` | several | numerals on abstract variables |
| five nonnegativity fields | several | likewise |
| `source_bound`, `remainder` | 1, 5 | **the Cauchy estimate** -- real content |
| `Sodd_enclosure` | 1 | real content, needed from above |
| the four sweeps | 2-3 each | finite but not kernel-computable |
| `NumericalFactsFull`'s eight extras | 1 each | the Arb sweeps, coupled to defined objects |

### Why S* is out of reach, corrected

An earlier note here reasoned that the geometric tail bound on the cCoeff is
too lossy to reach `S* <= 6.9764`.  That is wrong, and the arithmetic behind it
was wrong twice over.  `S*` is `sum_{i>=0} 2^i |c_i|`, whose head to `i = 30`
is `6.97633205` and whose total is `6.97633273`.  So:

| bound on the coefficients | tail from i=31 | smallest head cutoff that fits |
|---|---|---|
| `|c_i| <= 44.5987*3^-i` (Lemma 3.7(i) + Sigma_0) | 4.65e-04 | **i = 36** |
| `|c_i| <= 354.36*3^-i` (as stated in print) | 3.70e-03 | i = 41 |

against a budget of `6.9764 - 6.97633205 = 6.795e-05`.  I had quoted that
budget as `6.8e-06`, which is the TRUE tail beyond `i = 30` (`6.80e-07`)
confused with the room to `6.9764`, and had put the cutoff at `i ~ 42`.

The correction matters because it changes the diagnosis.  Thirty-six head
terms is a small number, so the tail is NOT the obstruction.  The obstruction
is `cCoeff` itself:

    noncomputable def cCoeff (i : ℕ) : ℂ :=
      iteratedDeriv i G2at1 0 / (Nat.factorial i : ℂ)

a Taylor coefficient of `G2at1`, the Euler-product function -- `G2at1 2` IS
`dConst`, by `G2at1_two_eq_dConst`.  It is defined through `iteratedDeriv`, so
there is nothing to compute for any `i`, cheaply or otherwise; a numerical
bound on `c_i` has to come from the Cauchy estimate on the contour, which is
the certified arc bound of Lemma 3.7 (`M = 326`) and so a hypothesis by
construction.  That is the
same wall as `Sodd`, and it is unlike `d` and `rho`, where the factors were
rational and a finite product settled a one-sided bound.

`Gam` deserves a note.  It appears ONLY in the two structure signatures, the
two theorem signatures, and `Gamma_bound` itself -- no other field mentions
it, and neither top-level theorem uses it.  So `Gamma_bound` constrains a
bound variable nothing reads.  It is kept because deleting it would leave the
manuscript's Theorem 6.1 constant with no Lean mirror, which is worse drift
than a vacuous one; `rho_enclosure` could go because a proved theorem took
over its mirroring duty.

## `rho_enclosure` was used nowhere either

`grep` for `rho_enclosure` and `rhoConst` across `Banksmartin/` and `Odd/`
returns the two field declarations and one comment.  No `hnum.rho_enclosure`
anywhere.  It is a hypothesis with no consumer, so it is not part of the
trusted base in any operative sense -- but it IS part of the three-way
correspondence CLAUDE.md protects, so it is flagged here rather than deleted.

## Tier C — partly closed, and the reason is sharper than "interval arithmetic"

**Infinite products over primes: CLOSED, both of them.**  `d_enclosure` and
`d_enc` are proved and gone (`dConst_lower_bound`, `dConst_lower_bound_sharp`).
This was supposed to need a verified interval layer and did not, for a reason
worth stating because it predicts which other items can fall:

    (1 - 2/p)^-1 (1 - 1/p)^2 = (p-1)^2/(p(p-2)) = 1 + 1/(p(p-2))

The Euler factor is **rational** -- no logarithm in it -- and every factor
EXCEEDS 1.  So a finite partial product bounds the infinite product from below
with **no tail estimate at all**, and the development only ever used `d` from
below.  The two-sided `5.3e-8` enclosure remains unreachable; the one-sided
bound is a finite rational computation.  94 primes (`p <= 499`) serve the
unrestricted side, 668 (`p <= 4999`) the odd side, the latter needing `simp`'s
step budget raised because a `Finset` literal dedups pairwise.

The lesson: the dividing line is not "analytic object vs explicit formula".
It is **whether the one-sided bound the proof actually uses can be reached by a
finite computation.**  `d` looked analytic and was arithmetic.

**`Sodd_enclosure`: genuinely out of reach, and now quantified.**
`Sodd = tsum over p >= 3 of log p/((p-1)(p-2))` is needed from ABOVE, so unlike
`d` the tail cannot be discarded -- every omitted term makes the bound wrong in
the dangerous direction.  The budget is tight: `betaOdd >= 0.1556` with the
proved `d >= 0.3786823` allows `Sodd <= 0.8593986514`, and the partial sum to
2,000,000 is already `0.8593917315`, leaving `6.9e-6` for the tail.  The actual
tail beyond 100,000 is `9.5e-6` -- still too big -- so primes past about
150,000 are required, roughly 13,800 terms, **each carrying a `log p` that
needs its own rigorous enclosure**, plus a Chebyshev-type bound to control what
is left.  For scale: 668 *rational* factors took 45 minutes of CI.  This is not
a budget away, it is a different problem.

**Contour suprema and derivative bounds.**  `M0_bound`, `g_deriv`,
`g_deriv_bound`, `alpha_dom`, `Sstar_dom`, `UV_bound`, `Eexp_bound`.  These
are the Arb sweeps, and these are the ones that genuinely couple an abstract
bound to a defined object.  `M0_bound` quantifies over every `theta` and every
`u > 1`.  (`Sstar_bound`, `alpha_bound`, `Gamma_bound` and `MR_bound` were
listed here in error -- see the section on the nine fields above.)

**The Cauchy estimate itself.**  `OddNumericalFacts.remainder` and
`NumericalFacts.source_bound` / `UV_bound` / `Eexp_bound`.  This is the
analytic heart, not a number: it is where complex analysis enters.

**The finite sweeps.**  `sweep_low` (6..199), `sweep_mid` (78..899),
`sweep_high` (900..2439), and the odd `sweep_low` (1..58).  These are finite --
2,490 and 58 instances -- so they are *in principle* decidable, but each
instance needs `f k` to enough precision, and `f` is not kernel-computable.
They would be the last thing to fall, not the first.

## The rule that predicts which fields can fall

Four fields fell in one session and three did not, and the difference is not
the taxonomy this document started with ("analytic object vs explicit
formula").  It is this:

**A field can be proved here exactly when the ONE-SIDED bound the development
actually uses is a finite computation on RATIONAL data.**

Both halves matter, and each is doing work:

*One-sided.*  `d` is used only from below, `rho` not at all, so the tail of
their infinite products could be discarded entirely -- every factor exceeds 1,
so a partial product is a bound with no estimate of what was dropped.  `Sodd`
is needed from ABOVE, so nothing can be discarded, and that alone moves it
from a 94-prime computation to one needing primes past 1.5e5 with a `log p` in
each of ~13,800 terms.

*Rational.*  `d` and `rho`'s Euler factors are `1 + 1/(p(p-2))` and
`1 + (3p-1)/(p^2(p-3))` -- exact rationals, so a partial product is an exact
rational and `norm_num` can compare it to a numeral.  `S*`'s coefficients are
`iteratedDeriv i G2at1 0 / i!`, where there is no computation to perform at
any `i`.  `Sodd`'s summands carry `log p`.  `fOdd k` and `f k` are infinite
sums whose terms carry `log n`.

So the remaining fields are not a tier away from falling; they fail the second
test outright, and no amount of compute changes that.  Closing any of them
means supplying the missing arithmetic -- verified interval arithmetic with
transcendental functions -- or formalizing the Cauchy estimates that produce
the bounds instead of computing them.  Those are projects, and this is the
honest boundary of what the technique reaches.

## Section 8 of the paper overstates the odd formalization

This is the one finding here that is a defect in the manuscript rather than in
the Lean, and it is the one worth acting on first.

Section 8 ("Certification and formalization") says:

> The analytic proof is the whole of Sections 2--6 apart from the two numerical
> propositions named below: in particular ... **the remainder reduction in
> Proposition~\ref{prop:odd-remainder}** ... These reductions are formalized in
> Lean 4 without `sorry`.

`prop:odd-remainder` is `|R_k| <= 4900 (k+3)^3 3^(-k)` for all k >= 1, proved
in the paper from the certified `M_R`.  In Lean it is not a theorem.  It is

    OddNumericalFacts.remainder : forall k,
      |fOdd k - 1/2 - betaOdd * (1/2)^k| <= MR * (k+3)^3 * (1/3)^k

an assumed field of the hypothesis structure, with `MR_bound : MR <= 4900`
pinning the constant.  Same statement, opposite status: the paper says proved,
the development assumes it.

Two further details sharpen this rather than soften it.

*The attempt existed and was empty.*  `fOdd_expansion_final` carries the
docstring "STEP 5, the target: this is exactly OddNumericalFacts.remainder" --
it is the theorem meant to discharge the field.  Until the radius fix it took
an unsatisfiable hypothesis (`DifferentiableOn C (Hodd s) (ball 0 4)`, false at
s = 1; see the section below), so it established nothing.  So the reduction was
not partly formalized; it was not formalized at all.

*Section 8's own framing excludes it.*  Section 8 says the numerical
propositions are exactly `prop:odd-certified` and `prop:full-certified`, and
that "the Lean formalization imports the resulting intervals as hypotheses".
`prop:odd-remainder` is neither of those two propositions, and it is not an
interval -- it is a bound quantified over all k.  So it is imported as a
hypothesis while sitting outside the category section 8 reserves for imported
hypotheses.

Not a divergence, checked: PROOF.md section 8 lists the sweep as "k = 1..75"
while Lean's `sweep_low` assumes only `1 <= k <= 58`.  Section 7 of PROOF.md
explains it -- the certified computation reaches 75, and 58 is what the
threshold K0 = 59 requires.  The numerics supply more than Lean asks for, which
is the harmless direction.

### What to do about it

Two options, and they are not equivalent.

1. **Formalize it.**  The radius repair in the companion branch removes the
   obstruction that made `fOdd_expansion_final` vacuous, so this is now
   reachable rather than blocked.  That would make section 8 true as written.
2. **Correct section 8.**  List `prop:odd-remainder` among the imported
   hypotheses.  One sentence, and it makes the paper accurate today.

CLAUDE.md says never to sharpen the paper alone; this is the reverse case -- the
paper currently claims MORE than the development delivers, so (2) removes a
defect rather than introducing a conservatism.  But it is a claim about the
project's own status in a co-authored manuscript, so it is flagged here and not
edited.  Doing (1) and leaving section 8 alone is the better outcome if the
work is going to happen anyway.

## The odd side assumes strictly more than the unrestricted side

The two structures look comparable by field count (4 odd, 13 unrestricted),
but they sit at different points in the same argument, and the odd one is
further back.

On the unrestricted side the Cauchy chain is FORMALIZED.  `M0_bound` assumes a
sup -- `forall u in Ioi 1, forall theta, ||G2manu u (circleMap 0 2 theta)|| <=
M0` -- and `gManu_eq_cauchy_coeff`, `lemma_3_8_integral_r1` (differentiation
under the contour integral) and `E1k_le_alpha` carry it to the coefficient
bound and then to `alph`.  Only the sup is trusted.

On the odd side the chain is absent and its CONCLUSION is assumed instead:

    remainder : forall k, |fOdd k - 1/2 - betaOdd * (1/2)^k|
                  <= MR * (k+3)^3 * (1/3)^k

and `MR_bound : MR <= 4900` only pins a numeral -- since `MR` is a parameter,
that field asserts nothing, and nothing anywhere in the structure says `MR`
bounds the sup of `|Htilde|`.  The link from the Arb-computed sup to the
remainder bound is a paper-level step with no Lean counterpart.  So the odd
side trusts the Cauchy estimate itself, not merely its numerical input.

### The scaffolding that looks like it closes this does not

`Odd/Basic.lean` has `HoddTilde_differentiableOn`, labelled "ITEM 2", which
would be the first link.  It is **used nowhere**, and two things are wrong
with it.  Both are now recorded in the Lean docstring as well.

*Its hypothesis is unsatisfiable where it matters.*  The lemma takes `hfac`,
the factorization, as a hypothesis for all `z` in `ball 0 4`.  But `HoddTilde
s z` is *defined* as `Hodd s z * (1 - z * 3^(-s))`, and at `z = 3^s` that
second factor is 0 while `Hodd`'s own p = 3 factor is `(1 - 1)` inverted,
which under Lean's `0⁻¹ = 0` is 0 rather than a pole.  So the left side is 0
there and the right side generically is not.  `3^s < 4` exactly when
`s < log 4 / log 3 = 1.26186...`, so for those s the bad point is inside the
ball and `hfac` is false.  `HoddTilde_factored`, two declarations above, does
not discharge it: it carries an `h3ne` hypothesis that fails at that same
point.  The lemma is therefore vacuous on the lower part of [1, 2] -- the
near-pole part, which is the part the argument needs.

*And the radius is too small anyway.*  `MR_bound` is a sup over |z| = 4.5.
That circle is not in `ball 0 4`, so even an unconditional ITEM 2 would not
reach it.  The file's own header docstring says "|z| = R < 5", so the `4` in
the statement appears to be an error rather than a deliberate choice.

### The route, which is a definition change

Define Htilde by its FACTORED form.  Its only pole is then the p = 5 factor's,
at |z| = 5^s >= 5, so it is differentiable on `ball 0 5` -- which contains the
4.5 circle -- and the `3^s` problem does not arise because no inverted p = 3
factor appears.  Then relate it to `Hodd s z * (1 - z * 3^(-s))` away from
`z = 3^s`, where the singularity is genuinely removable.

That is the honest prerequisite for `remainder`, and it is a port of machinery
that already exists on the unrestricted side rather than new mathematics --
which makes it the most tractable of the remaining items, and the one I would
do next.  It does not close `remainder` by itself: that still needs the
representation theorem linking `fOdd`'s coefficients to Htilde's, which is
where the real work is.

## One load-bearing field is not a numerical fact at all

`Gamma_bound` turned out to be vacuous.  `g_deriv` is the opposite error and
the more serious one: it is load-bearing, and it is not numerics.

    g_deriv : forall i, forall x in Ioo 1 2,
      HasDerivAt (gManu i) (deriv (gManu i) x) x

`HasDerivAt f (deriv f x) x` holds exactly when `f` is differentiable at `x` --
if it were not, `deriv f x` would be `0` and the statement would be false.  So
the field asserts that `gManu i` is differentiable on `(1, 2)`.  That is a
limit existing.  An Arb ball computation bounds a quantity; it cannot show a
limit exists, so NO run of the certified package establishes this field, and
rerunning the package with more precision will never close it.

It is used (via `source_bound_full`, at the `NumericalFactsFull` call site), so
unlike `Gamma_bound` it cannot simply be deleted.

This matters because it misstates who owns the obligation.  `NumericalFacts`'s
docstring says "each field is an Arb ball computation from the companion
package, exactly the division Caveat 1.3(b) draws."  For `g_deriv` that is
false, and the consequence is practical: a reader auditing the trusted base
would look for the Arb script behind it and find none, and a maintainer would
try to discharge it by recomputation, which cannot work.  The Lean docstrings
for the structure and the field now say so.

**This affects the manuscript's Caveat 1.3b as well**, which draws the same
division between "machine-verified analytic reduction" and "certified
numerics".  `g_deriv` sits on the numerics side of that line and does not
belong there -- it is an analytic assumption.  Changing Caveat 1.3b's wording
is not a change I should make unilaterally, so it is flagged here rather than
edited: the paper currently understates, by one field, how much is assumed
mathematically rather than computed.

For scale, the proof that would close it: `G2manu s z = (kappaFac s)^z *
G2C s z`, so `gManu i s` is the i-th z-derivative at 0 of that product over
`i!`, and differentiability in `s` requires differentiating an Euler product
under the iterated-derivative operator -- comparable work to `source_bound`,
not a tidy-up.

## Verified arithmetic would not close the sweeps, and this is why

The paragraph above is easy to misread as "get verified interval arithmetic
into the development and the sweeps fall."  They do not, and the reason is
structural rather than a matter of degree.

`sweep_low` and its two siblings assert `f k < f (k + 1)` over a finite range
of `k`.  Finitely many instances, so the instinct is that a strong enough
evaluator discharges them one at a time.  But look at what one instance says.
By `lemma1_foundation`,

    f k = Ik k + Tk k
    Ik k = integral over Ioc 1 2 of Fk k s        -- a Bochner integral
    Tk k = tsum over {n // 2 <= n and bigOmega n = k} of 1/(n^2 * log n)

So a single instance of a sweep compares two Lebesgue integrals plus two
infinite sums over Omega-classes, each summand carrying a `log n`.  That
proposition is not DECIDABLE -- there is no `Decidable` instance, and there
could not be one.  Finiteness in `k` buys nothing, because the object sitting
at each `k` is itself infinite in two separate ways.

This matters for the tool question specifically.  `native_decide` evaluates
decidable propositions; it cannot be pointed at `f k < f (k + 1)` at all, at
any depth or any budget.  Neither can `decide`, `norm_num`, or `leancert`'s
checkers.  Verified interval arithmetic is the machinery at the BOTTOM of a
proof that has already reduced the statement to rational data -- it is not a
way to get there.  The reduction is the missing work:

  1. a rigorous Lean enclosure of `Ik k`, i.e. numerical integration with
     certified error, for the specific integrand `Fk k`; and
  2. a rigorous tail bound on `Tk k` over `{bigOmega n = k}` -- the same
     Omega-class tail that Section 5's delta-table handles numerically.

Neither exists in Mathlib, and `leancert` supplies neither: its machinery is
Chebyshev/Mertens prime sums and Abel summation, not integration over an
interval against an arbitrary integrand.  `source_bound` is in the same
position for the same reason, with the extra difficulty of being infinite in
`k` as well.

The practical consequence is that the trust decision below -- whether to
accept `Lean.ofReduceBool` in exchange for `native_decide` -- **does not need
to be made yet**, because no currently remaining field would be closed by
making it.  It becomes live only after (1) and (2) exist, at which point the
reduced statement is rational and the question of which evaluator discharges
it is finally the operative one.  That ordering is worth being explicit about:
it would be easy to spend the trust and gain nothing.

## The route to an instance, and the trust decision it forces

The structures have NO INSTANCE -- every occurrence in the development is a
hypothesis binder.  So "completely formalized" means exactly one thing:
produce an instance of `NumericalFactsFull` and `OddNumericalFacts`, at which
point the theorems become unconditional.  Note that the numeral fields are
FREE once you instantiate (take `Sstar := 6.9764` and `Sstar_bound` is
`le_refl`); the work is entirely in the coupling fields -- `Sstar_dom`,
`alpha_dom`, `UV_bound`, `M0_bound`, `Eexp_bound`, `g_deriv` -- plus
`Sodd_enclosure`, the Cauchy estimates, and the sweeps.

**`leancert` exists and is referenced here, but is NOT currently usable.**  It
is in `lake-manifest.json` with `inherited: true`, pulled in transitively, but
`import LeanCert` FAILS: the module is not on the search path, because nothing
imports it and so Lake never builds it --

    No directory 'LeanCert' or file 'LeanCert.olean' in the search path
    probe/leancert.lean:21:0: error: unknown module prefix 'LeanCert'

verified by probe rather than assumed.  Using it would take an explicit
`[[require]]` in `lakefile.toml` and a from-source build on every CI run, and
whether rev `87a21d739dde` compiles against Mathlib `v4.33.0-rc1` is still
unknown -- LeanCert's HEAD pins toolchain `v4.35.0`, and the anonymous git lane
will not serve that sha to check.  What it provides, read from HEAD and so also
unconfirmed at the pinned rev: verified interval
arithmetic with `exp`, `log`, `sqrt`, `atan`; a `leancert` tactic for
quantified bounds over real intervals; certified partition integration; and --
directly relevant -- `LeanCert/ANT/Mertens.lean` and
`LeanCert/Engine/Chebyshev/{Theta,Psi}.lean`, with `logPrimeLB/UB p depth`
giving RATIONAL enclosures of `log p` and a general Abel-summation checker
over any rational weight.  No `sorry` in the Mertens module.  (The
`CertifiedBounds/Li2` interface does carry deliberate `sorry`s -- that module
must not be imported here.)

What that buys, item by item:

| obligation | status against this route |
|---|---|
| `alpha_dom`, `UV_bound`, `M0_bound`, `Eexp_bound`, `g_deriv_bound` | boxed suprema with `exp`/`log` -- the tactic's design target |
| `Sodd_enclosure` | head is `sum logPrimeUB p depth / ((p-1)(p-2))`; see the tail below |
| `Sstar_dom` | still blocked: `cCoeff` is `iteratedDeriv`, nothing to evaluate |
| `source_bound`, `remainder` | still blocked: Cauchy estimates, analysis not computation |
| the four sweeps | downstream of the above |

The `Sodd` tail is the interesting case, and it is closer than this document
previously claimed.  LeanCert's `verify_all_theta_*` theorems are all FINITE
range (`N <= bound`), so the unbounded tail needs an unconditional Chebyshev
bound, which Mathlib supplies via `primorial_le_4_pow` (`theta x <= x log 4`).
Partial summation against `w(x) = 1/((x-1)(x-2))` then gives a tail of about
`2c/N`, so the admissible `6.9e-6` needs `N` near `2.9e5` -- roughly 25,000
primes in the head.  LeanCert's own Chebyshev tests run at `N` from 599 to
7690, so this is three to four times beyond demonstrated scale rather than
orders of magnitude.  That is a real engineering question, not a wall.

**The route very likely runs on `native_decide`, though this is not yet
measured.**  There are 430 uses of it in LeanCert and the Chebyshev
certificates are discharged that way.  But a grep count is not a dependency:
the bound theorems themselves -- `log_prime_le_logPrimeUB`,
`mertensLogSum_le_mertensLogSumUpperRat` -- are ordinary proved inequalities
with no decidability in them, and `native_decide` enters only where a
`check... = true` hypothesis must be evaluated.  So the axiom cost is plausibly
zero for the proved bounds and nonzero only at the numeric step.  Which it is
decides how much of this can stay in the kernel, and it has NOT been
established: the probe that would have answered it could not get as far as
importing the library.
`native_decide` adds `Lean.ofReduceBool`, which the axiom audits in this
repository are written to REJECT -- they require exactly `[propext,
Classical.choice, Quot.sound]`.

So adopting this route is a decision about what the formalization means, and it
is not mine to make.  What should be said in its favour, though, is that it
would be a STRENGTHENING rather than a weakening of the present position.
Today the numerical propositions are certified by Arb through python-flint, by
scripts in `numerics/`, with the resulting constants transcribed into Lean by
hand as hypotheses -- so the trusted base includes Arb, python-flint, those
scripts, and the transcription, and Lean checks no number at all.  Under
`native_decide` the trusted base would instead be Lean's compiler evaluating a
checker whose correctness is a kernel-proved theorem.  That is strictly less to
trust, even though it is not kernel-pure, and Caveat 1.3b would need rewriting
rather than merely weakening.

The alternative is kernel-mode only, which keeps the axiom set exactly as it is
and caps what can be certified at whatever `decide` will evaluate -- far below
`N = 2.9e5`.

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
about what is machine-checked.

Tiers A and B are closed, and so is the prime-product half of Tier C.  Three fields left the base: two `forall`-statements about
a quadratic, which no finite computation could ever have discharged and which
a reader could not have checked by inspection, and one constant that Mathlib
could supply all along.  What replaced the first two is five scalars the
numerics already certify -- a `forall` is a much larger thing to be asked to
believe than a number, so the trade is real even though the field count barely
moved.

What is left in the base is exactly Tier C, and every item in it is there for
the same reason: it is a fact about an analytic object -- an infinite product
over primes, a supremum over a contour, a Cauchy estimate -- and not a fact
about an explicit formula.  Closing any of it means building verified interval
arithmetic in Lean.  That is a project in its own right, not a loose end of
this one.
