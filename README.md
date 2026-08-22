# The Erdős sums of almost primes increase strictly from k = 6

A Lean 4 formalization of the analytic reduction in *The Erdős sums of almost
primes increase strictly from k = 6* (Padhi–Lichtman), which disproves the
Banks–Martin conjecture, together with the certified computations it depends on.

## The theorem

    theorem erdos_sums_increase_from_six (Sstar alph Gam Umax Vmax : R)
        (hnum : NumericalFacts Sstar alph Gam Umax Vmax) :
        forall k, 6 <= k -> f k < f (k + 1)

where f k is the sum of 1/(n log n) over n >= 2 with Omega(n) = k.

Zero sorries.  Axioms: propext, Classical.choice, Quot.sound.

## Two forms of the theorem

    erdos_sums_increase_from_six       (Sstar alph Gam Umax Vmax) (NumericalFacts ...)
    erdos_sums_increase_from_six'  (beta Sstar alph Gam Umax Vmax M0) (NumericalFactsFull ...)

Same conclusion.  They differ in how much of the analysis is *used*.

The first takes the section 7 source bound as a single assumed field
(`source_bound`).  Short hypothesis list, but Proposition 2.5, Theorem 4.1 and
section 3.5 are then proved and unreferenced.

The second replaces that field with the quantities the Arb package actually
computes -- the beta_i sweep, M_0, the S* and alpha partial-sum bounds, the U/V
and E_exp sources -- and *derives* the source bound from them via
`source_bound_full`.  Its dependency chain reaches Proposition 2.5 (the exact
decomposition), Theorem 4.1 (through `deltaM_abs_le` and `deltaConv_le`) and
section 3.5 (through `E1k_le_alpha`).

The primed form is the one that demonstrates the formalization is doing work.
The unprimed form is kept because it is easier to instantiate and states the
same theorem.

Theorem 6.1 (the refined enclosure) is consumed by `E1k_le_refined`, which
combines it with `A2m_le` to give |E_1(k)| <= (Bhat/2)(k+1) + Gamma.  That is
the bound behind the manuscript's K0 = 79; the coverage of [79,899] itself
comes from the certified sweep, which no formalization can replace.

## What is proved, and what is assumed

MACHINE-CHECKED, in Banksmartin/Basic.lean:

  * Section 2, the exact reduction: Lemmas 2.1, 2.2, 2.4, Proposition 2.5, and
    both coefficient identities (sum c_i = 1/2, sum 2^i c_i = d)
  * Section 3: Lemma 3.9 (real and complex), Lemma 3.8 at r = 1 and r = 2,
    section 3.5's mean-value step, manuscript (4) and (10), |E_1(k)| <= a+(k+1)
  * Section 4: Theorem 4.1, both bounds
  * Section 6: Theorem 6.1, including the k-independence of Gamma
  * Section 7: Theorem 7.1, and the four-range assembly

ASSUMED -- the NumericalFacts structure.  Its fields are the Arb ball
computations in numerics/: the constant enclosures, the beta_i and gammahat_i
sweeps, U_max and V_max, phi(2440) > 0 with its monotonicity, and the criterion
sweeps over [6,199], [79,899] and [900,2439].

NumericalFacts has no Lean instance and cannot have one: sweep_low and its
siblings quantify over f k, an infinite sum over {n : Omega(n) = k}, which no
proof assistant evaluates.  The theorem is conditional by construction -- the
division Caveat 1.3(b) of the manuscript already draws.

## Constants

The formalization takes these as parameters; the numerics certify them.  All
four improve on the manuscript, because the sweeps were rerun at documented
settings that are tighter than the ones originally used:

| | manuscript | this repository |
|---|---|---|
| alpha_+ | 15.5716 | 15.4257 |
| Gamma | 105.4060 | 104.5196 |
| K0 | 79 | 78 |
| K1 | 2440 | 2433 |

See numerics/README.md for the settings and how they were recovered.

## Verifying

    lake build
    #print axioms erdos_sums_increase_from_six
    cd numerics/bm-rebuild-v21 && python3 ../verify.py

verify.py checks the Arb output against theorems proved here: Theorem 4.1's
delta bound over 2441 entries, A2m_le, the Cauchy tails, Gamma's recomposition,
and the sweep coverage.  Passing means the two halves describe the same objects.

## What the formalization found

Three convergence gaps invisible on paper, each making a downstream statement
vacuous until closed:

  * cFac's multipliability -- Lemma 2.2's hypotheses
  * dConst's convergence -- d_enclosure was a claim about a junk value
  * Sm's integrability -- LOAD-BEARING under Am, delta_m and Theorem 4.1

## The odd companion

    theorem fOdd_decreasing (MR : R) (hMR0 : 0 <= MR) (hnum : OddNumericalFacts MR) :
        forall k, 1 <= k -> fOdd (k + 1) < fOdd k

where fOdd k restricts the sum to ODD n >= 3.  Lichtman's conjecture is that
removing the prime 2 -- which is what drives the increase in the main theorem --
restores the decrease.  Zero sorries; the same three axioms.  See odd-proof/PROOF.md
for the argument and odd-proof/numerics/README.md for the certified inputs.

The remainder bound |R_k| <= C (k+3)^3 3^-k holds with C = 4900, giving the
analytic threshold K0 = 59.  C is derived rather than fitted: it is the sum of
the Lagrange-remainder term CE*S/18, the two coefficient tails S_0/2 and
9S_1/128, and the near-region contributions CN and NEARU, each a certified
interval computation.

## Layout

    Banksmartin/Basic.lean       the main development (~13k lines)
    Banksmartin/EulerGamma.lean  Euler's integral identity, built from scratch
    Odd/Basic.lean               the odd companion (~8.9k lines)
    numerics/                    certified computations for the main theorem
    odd-proof/PROOF.md                 the odd argument, sections 1-8
    odd-proof/numerics/                certified computations for the odd theorem
    odd-proof/axcheck.lean             axiom audit: lake env lean odd-proof/axcheck.lean
    paper/proof.tex              the joint write-up
    HANDOFF.md                   design decisions and Lean-specific lessons

## Building

Requires the toolchain in lean-toolchain and the Mathlib revision in
lake-manifest.json.  Run "lake exe cache get" then "lake build".
