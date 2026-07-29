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

## Layout

    Banksmartin/Basic.lean       the development (~13k lines)
    Banksmartin/EulerGamma.lean  Euler's integral identity, built from scratch
    numerics/                    certified computations; see numerics/README.md
    HANDOFF.md                   design decisions and Lean-specific lessons

## Building

Requires the toolchain in lean-toolchain and the Mathlib revision in
lake-manifest.json.  Run "lake exe cache get" then "lake build".
