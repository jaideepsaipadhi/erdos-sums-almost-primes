# The odd Erdős sums

    fOdd k  =  sum over odd n >= 3 with Omega(n) = k of 1/(n log n)

CONJECTURE (Lichtman, 2026-07-29): `fOdd k` is strictly decreasing for all k.

The main theorem of this repository disproves Banks–Martin: `f k` is strictly
*increasing* from k = 6.  The suspicion is that the prime 2 is responsible --
n = 2^k dominates f k -- and that removing it restores the conjectured
decrease.  This directory is the proof that it does.

## What is here

    PROOF.md          the argument, sections 1-8.  Start here.
    numerics/         the certified inputs; see numerics/README.md
    axcheck.lean      axiom audit -- `lake env lean odd-proof/axcheck.lean`
    NOTES.md          status notes
    superseded/       earlier approaches, kept for provenance

The Lean development is `Odd/Basic.lean` at the repository root.

## The result

    theorem fOdd_decreasing (MR : R) (hMR0 : 0 <= MR) (hnum : OddNumericalFacts MR) :
        forall k, 1 <= k -> fOdd (k + 1) < fOdd k

Zero sorries; axioms `propext`, `Classical.choice`, `Quot.sound` only.  As with
the main theorem, `OddNumericalFacts` has no Lean instance and cannot have one:
its fields quantify over `fOdd k`, an infinite sum no proof assistant evaluates.

## The shape of the argument

Write `R_k = fOdd k - 1/2 - beta 2^-k`.  Section 5 proves

    |R_k| <= C (k+3)^3 3^-k,   C = 4900,

and section 6 combines it with `beta 2^-(k+1)` to give the decrease for
k >= 59, the certified sweep covering the rest.

C is derived, not fitted.  It is

    CE*S/18  +  S_0/2  +  9*S_1/128  +  CN  +  NEARU
    = 4395.5 +   22.3  +     46.1    + 367.8 + 26.1  =  4857.9,

the Lagrange remainder, the two coefficient tails, and the near region.  Every
constant is a certified interval computation with a script and a log in
`numerics/`.  Earlier drafts folded the last four into an unquantified
"(lower order)" and reported C = 2402.3 with K0 = 57; section 5.1 records what
that omitted.

## Superseded

`superseded/README-g_k-route.md` is the earlier plan, which went through
`fOdd k = f k - g_{k-1}` with `g_k = int_1^inf 2^-s P_k(s) ds`.  The current
proof works with `fOdd k` directly.
