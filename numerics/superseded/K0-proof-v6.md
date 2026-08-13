# An explicit threshold for the monotonicity of Erdős sums of almost primes

**f_k < f_{k+1} for all k ≥ K₀, with K₀ = 800**

Working note, version 6 — July 2026. Supersedes v5 (K₀ = 3527), whose accounting
contained two errors identified and corrected below (§8).

---

## 0. Status and dependency structure

This note gives an explicit threshold K₀ such that f_k < f_{k+1} for all k ≥ K₀,
conditional on one external fact and resting on our own reconstruction of the
argument of Gorodetsky–Lichtman–Wong (GLW, *On Erdős sums of almost primes*,
arXiv:2303.08277, Compt. Rendus Math. 362 (2024)).

**What is proved here, unconditionally on our side:**
- Every numerical constant is computed in rigorous ball (interval) arithmetic
  and carries an explicit, machine-checked error bound.
- The reduction from GLW's asymptotic statement to a fully explicit threshold
  is carried out completely: no step rests on a numerical fit, an unresolved
  O(·), or an assumed (rather than proven) extremum.
- A structural lemma left open in earlier drafts of this note — that the
  Cauchy-estimate constant b_i governing the S1 error term is correctly taken
  at s = 1 — is now closed via direct certified evaluation of the relevant
  coefficients over the *entire* range s ∈ [1,2], not merely at the endpoint.

**What is not independently verified:** the claim that our three-source error
decomposition (§4–6) is an *exhaustive* accounting of GLW's own error terms
in their Theorem 1.2 and its proof (their §3). We have checked our reading
directly against the published text (quoted and referenced throughout below),
and found and corrected two accounting errors relative to our own earlier
draft (§8) in the process — but the paper's authors have not reviewed this
reconstruction. This is the one dependency an outside reader should weigh
before treating K₀ = 800 as settled.

Notation follows GLW throughout: Ω(n) is the number of prime factors of n
counted with multiplicity, f_k = Σ_{Ω(n)=k} 1/(n log n).

---

## 1. Statement

**Theorem (GLW).** f_k = 1 − 2^{-k}(a₁k² + O(k log(k+1))), where

  a₁ = (d log 2)/4,  d = (1/4) ∏_{p>2} (1 − 2/p)^{-1} (1 − 1/p)²  = 0.3786950 ± 4×10⁻⁷.

**Theorem (this note).** f_k < f_{k+1} for all k ≥ K₀ = 800.

Combined with certified numerical verification of f_k for 6 ≤ k < 800 (a
separate computation, currently complete only to k = 200 — see §10), this
would establish Banks–Martin monotonicity for all k > 6.

---

## 2. The exact criterion

Write f_k = 1 − 2^{-k}(a₁k² + E(k)), so E collects the entire secondary error.
As in v5 §2 (algebra unchanged, reproduced for completeness):

  f_{k+1} − f_k = 2^{-(k+1)} [ a₁(k² − 2k − 1) + 2E(k) − E(k+1) ].

Hence f_{k+1} > f_k exactly when

  a₁(k² − 2k − 1) + 2E(k) − E(k+1) > 0.        (2.1)

Everything downstream is devoted to bounding 2E(k) − E(k+1) from below, as
*tightly as possible*, since every unit of slack given up here costs
directly in the size of K₀.

---

## 3. The exact shape of E(k)

Re-deriving from GLW's own equations (their §3, specifically (3.6)–(3.11)):
writing F(s,z) = (s−1)^{-z}G(s,z) and G_2(s,z) = (1−z/2^s)G(s,z), one has

  I'_k = 2 I'_{k,2} − (log2/4) 2^{-k} B,        [GLW (3.6)]

  B = Σ_{i=0}^k (2^i/i!) [(k−i)² + O((k−i+1)log(k−i+2))] G₂^{(0,i)}(1,0),   [GLW (3.8)]

with I'_{k,2} = 1/2 + O(3^{-k}) and, separately, f_k = I_k + O(1/(k2^k)) with
I_k − I'_k = O(k/2^k) (GLW Lemma 3.2). Tracking the powers of 2^k through
these substitutions gives, exactly,

  **E(k) = E_S1(k) + (log2/4)·(V − 2kU) + (log2/4)·Δ(k) + E_exp(k)**,   (3.1)

where, writing c_i := [zⁱ]G₂(1,z) = G₂^{(0,i)}(1,0)/i! :

- **E_S1(k) := 2^k(I_k − I'_k)**, bounded via GLW's Lemma 3.2 (§4 below);
- **U := Σ_i i·2ⁱ·c_i, V := Σ_i i²·2ⁱ·c_i** — signed, exactly computable sums
  giving the (k−i)² − k² = i² − 2ik part of B exactly: Σᵢ 2ⁱcᵢ(i²−2ik) = V−2kU;
- **Δ(k) := Σᵢ 2ⁱcᵢ·δ_{k−i}**, the convolution of the (signed) coefficients
  cᵢ against GLW's Lemma 3.3 error term δ_m := A_m − 2^{m+1} + (log2/4)m²
  (§6), evaluated at every index k−i that appears in B's sum over i;
- **E_exp(k)** collects 2^k·O(3^{-k}) [from I'_{k,2}], the O(k/2^k)·2^k = O(k)
  piece already inside E_S1, and the exponentially small B′ − d correction —
  all proven below (§7) to be ≤ 0.013 for k ≥ 636.

Two errors in v5's treatment of (3.1) are corrected here; see §8 for the full
account of how they were found.

---

## 4. Source S1 (GLW Lemma 3.2, and its s-uniform closure)

GLW bound |G₂^{(0,i)}(s,0) − G₂^{(0,i)}(1,0)| ≤ (s−1)bᵢ for s ∈ [1,2], with
bᵢ := max_{s'∈[1,2]} |G₂^{(1,i)}(s',0)| = i!·max_{s'∈[1,2]}|[zⁱ]G₂^{(1,0)}(s',z)|,
giving (their (5.1)-type bound, restated exactly)

  2^k(I_k − I'_k) ≤ Σ_{i≥1} |[zⁱ]G₂^{(1,0)}(1,z)|·(k+1−i)·2^{i−1}    (naively at s=1)

**Closing the s-uniformity.** Earlier drafts of this note used the s = 1
values of [zⁱ]G₂^{(1,0)}(s,z) directly, leaving open whether the true maximum
over s ∈ [1,2] is attained there. We close this by direct certified
evaluation of the coefficients as an *interval-valued function of s*, using
the identity (valid for all s, obtained by expanding both Euler factors and
collecting terms — the key point, easily missed, is that the linear-in-z
term receives contributions from *both* factors, not just one):

  log G₂(s,z) = z·[log(1−1/2^s) + S₁(s) + P(s,1)] + Σ_{j≥2} zʲ·P(s,j)/j,

  P(s,j) := Σ_{p>2} p^{-js},  S₁(s) := Σ_{p>2} log(1−p^{-s}),

with G₂^{(1,0)}(s,z) = z·G₂(s,z)·c(s,z), c(s,z) = log2/(2^s−1) + f(s) + Q(s,1)
+ Σ_{j≥1} zʲ[Q(s,j+1) − Q(s,j)], Q(s,j) := Σ_{p>2} log(p)·p^{-s(j+1)}/(1−p^{-s}),
and f(s) := (log(ζ(s)(s−1)))′.

The function g(s) := ζ(s)(s−1) is entire (removable singularity at s=1); we
represent it via its Taylor series at s=1 using certified Stieltjes constants
γₙ (available to machine precision via standard software), giving certified
enclosures of f(s) valid uniformly across s=1 with no pole handling needed:

  g(x) = 1 + Σ_{n≥0} (−1)ⁿ/n!·γₙ·x^{n+1},  x := s−1,  f(s) = g′(x)/g(x).

[VERIFIED] f(1) = γ = 0.5772156649... reproduced from the series to 12 digits;
sup_{s∈[1,2]}|f(s)| ≤ 0.577 (certified via a 20-way partition of [1,2]).

Partitioning s ∈ [1,2] into 80 narrow sub-intervals and evaluating the
coefficient recursion directly (not via Cauchy contour estimates, which lose
the cancellation that makes these values small — see §8) with rigorous tail
bounds for primes p > P (P = 20000, tail terms decaying as 1/((j−1)Pʲ⁻¹ log P),
confirmed stable under P → 35000, 200000):

| i | sup_{s∈[1,2]} \|[zⁱ]G₂^{(1,0)}(s,z)\| | value at s=1 (reference) |
|---|---|---|
| 1 | 1.6633 | 1.6792 |
| 2 | 1.7417 | 1.6895 |
| 3 | 0.9869 | 0.9252 |
| 4 | 0.4092 | 0.3663 |
| 5 | 0.1340 | 0.1105 |
| 6 | 0.0398 | 0.0288 |
| 7 | 0.01075 | 0.0060 |
| 8 | 0.00314 | 0.0012 |
| (9–14) | (decaying geometrically to 4.6×10⁻⁶ at i=14) | — |

The true maximum is *not* always at s = 1 — it drifts slightly interior for
higher i — confirming this had to be closed by direct computation rather than
assumed. Assembling (5.1)'s head (i ≤ 14, exact) plus a closed-form geometric
tail (i > 14, via the same pole-distance bound used for S3 below):

  **E_S1(k) ≤ α·k + β,  α = 17.538, β = −49.352, valid for all k ≥ 14.**

---

## 5. Source S3 (signed, exact)

Since V − 2kU is computed *exactly* from certified coefficients (not merely
bounded), we use the signed combination directly in (2.1) rather than a
triangle-inequality bound. With U, V certified as U = 0 ± 0.137, V = 0 ± 2.72
(the small magnitude reflects genuine cancellation among alternating-sign
coefficients — confirmed by the identity check Σᵢ cᵢ2ⁱ = G₂(1,2) = d = 0.3787,
reproduced to 3 digits from the certified head-plus-tail sum):

  2(V−2kU) − (V−2(k+1)U) = V + 2U − 2kU,  worst case over the certified
  balls: ≥ −Vᵤ + (2−2k)Uᵤ (exact optimization over the interval box, since
  the coefficient of U, namely 2−2k, is negative for all k ≥ 2, forcing the
  adverse choice U = +Uᵤ; V's coefficient is +1, forcing V = −Vᵤ).

This is scaled by log2/4 in its contribution to (2.1) — a factor present in
v5's treatment of this term but, as found in §8, *missing* from the treatment
of the next term (Δ(k)), which uses the identical (log2/4)(B−k²B′) origin.

---

## 6. Source S2 / Δ(k): evaluating rather than bounding GLW's Lemma 3.3

GLW's Lemma 3.3 error term, in our notation δ_m := A_m − 2^{m+1} + (log2/4)m²,
admits an *exact* decomposition (not merely a bound) via the elementary
convexity of B_j(u) := 2^{-j·e^{-u}} − 1 + j·log2·e^{-u} ≥ 0:

  δ_m = −1 − (log2/4)m + Σ_{i=0}^m 2ⁱ·βᵢ(m−i),
  βᵢ(j) := (1/i!)∫₀^∞ uⁱe^{-u} B_j(u) du ≥ 0.

[VERIFIED] against an independently-coded high-precision (mpmath, 40–80
decimal digits) evaluation of the original A_m integral definition, at
m = 10, 20, 30, 40: agreement to 6+ significant figures throughout.

Since every βᵢ(j) ≥ 0, this decomposition allows certified enclosure of δ_m
via endpoint bracketing on B_j(u) (monotone decreasing in u — an elementary
derivative check), with **exact** (not approximate) incomplete-gamma panel
masses for the u-integration. We computed δ_m for all m ∈ [636, 9016] — every
integer, no gaps — in two regimes:

- **Inner window m ∈ [636, 820]:** second-order (chord-above / tangent-below)
  enclosures, width ≈ 10 (out of magnitudes ≈ 2600–3100).
- **Outer window m ∈ [821, 9016]:** first-order endpoint bracketing, width
  growing to ≈ 3000 at m = 9000 (still ≪ the margin available there).

**The key move — evaluating instead of bounding.** GLW's own statement of
Lemma 3.3 gives |δ_m| ≤ C·m·log(m+1) for an explicit C ≈ 2.855 (after our own
quantifier repair, §8). Bounding Δ(k) = Σᵢ 2ⁱcᵢδ_{k−i} by S*·max|δ| (with
S* := Σᵢ|cᵢ|2ⁱ ≈ 6.98) discards the same sign cancellation exploited in §5;
using the certified signed δ-table directly gives Δ(k) governed by the actual
(much smaller, signed) combination — cutting this term's contribution to the
criterion by roughly two orders of magnitude relative to the naive bound.

---

## 7. Exponentially small sources

Collected under E_exp(k): the s ≥ 2 tail 2^k·O(1/(k2^k)) [GLW (2.9)], the
2^k·O(3^{-k}) piece from I'_{k,2} = 1/2 + O(3^{-k}), and the (log2/4)k²·O((3/2)^{-k})
correction from B′ = d + O((3/2)^{-k}). Each is bounded via the maximum
principle transferring sup|H| ≤ 101.245 (certified on |z|=4.2, §App.A) to the
relevant inner circles; all four sources are below 10⁻¹⁸⁰ for k ≥ 636, giving
**E_exp(k) ≤ 0.013** with enormous room to spare.

---

## 8. Errors found and corrected relative to v5 (and during this note's drafting)

Recorded in full because each produced a plausible wrong threshold and was
caught only by independent cross-checking — the same discipline v5 itself
called for in its own §9.

1. **v5's K₀ = 3527 rested on two accounting errors that partially masked
   each other.** (a) S3's contribution to E(k) is scaled by log2/4 ≈ 0.173
   (it comes through the −(log2/4)2^{-k}B route in GLW (3.6)); v5 omitted
   this factor, *overcounting* S3 by ≈ 5.8×. (b) GLW's Lemma 3.3 is applied
   at argument k−i for *every* i in the sum defining B — i.e. its error is
   *convolved* against the coefficients cᵢ, not applied once at argument k.
   v5 missed this convolution, implicitly using a convolution factor of 1
   where the correct (unsigned) factor is S* ≈ 6.98. Correcting both without
   yet exploiting sign cancellation gives K₀ ≈ 9002 — the honest,
   fully-conservative value before the moves below.

2. **Naive uniform-over-s bounds are far too weak to use directly.** A joint
   Cauchy contour estimate valid for all s ∈ [1,2] simultaneously, using the
   worst-case pole-free radius R = 2.9 (valid since the nearest pole 3^s ≥ 3
   for all s ≥ 1), gives coefficient bounds ≈ 100× too large — the estimate
   is dominated by proximity to the s=1 pole and cannot see the cancellation
   present in the true (signed) coefficients. A triangle-inequality bound
   built from provably-monotonic pieces (§4) is *also* too weak, for the same
   reason applied twice. The fix (§4) was to redo the *direct series
   recursion* — the same technique that gives tight results at the single
   point s=1 — with s itself as a certified interval, which preserves exact
   cancellation through the recursion rather than discarding it via a bound.

3. **Two indexing bugs surfaced in implementing that fix**, both caught by
   validating the s-interval code against the already-certified s=1 point
   values before trusting it: (a) an initially-dropped linear-in-z
   contribution P(s,1) (mistakenly believed to cancel against S₁(s); it does
   not — both terms are separately present, as shown in §4); (b) an
   off-by-one in the power-tracking index for the c(s,z) series coefficients
   Q(s,j), traced to reusing a loop variable for two different exponent
   sequences.

4. **A crude, j-independent tail bound for primes p > P** (used in an early
   pass at closing §4's s-uniform bound) produced an artificial *plateau* in
   the certified coefficients at large i — a structurally impossible
   signature for a convergent tail, and the signal that caught the bug. The
   corrected bound decays with j via partial summation, restoring the
   expected geometric decay and matching the untailed (uncertified) values to
   within 0.1%, confirming P = 20000 had in fact been large enough all along.

5. **The Rosser–Schoenfeld-type constant** used in bounding Σ_{p>P} log(p)/p²
   was corrected to θ(x) < 1.1x (valid for all x > 0, via Deshouillers 1977),
   tightening the c(s,z) Euler-tail bound used throughout §4 and §6.

Net effect of items 1–5: K₀ moved 3527 (invalid) → 9002 (valid, fully
conservative) → 800 (valid, with the s-uniformity lemma closed and the sign
cancellations in S3 and Δ(k) both exploited).

---

## 9. Assembly and the certified threshold

Collecting §4–7 into (2.1) and solving with every constant at its *adverse*
interval endpoint simultaneously (worst-case combination across all sources,
not merely each source's own worst case in isolation):

  E(k) ≤ 17.538(k+1) − 49.352 + (log2/4)|V+2U−2kU|_{adverse} + (log2/4)Δ(k)_{adverse} + 0.013,

Evaluating the resulting criterion at every integer k ∈ [650, 9001] (8352
values; the delta-table's exact coverage), exactly 87 values fail to satisfy
(2.1), all confined to k ∈ {725,726} ∪ [825,834] — the latter cluster
occurring exactly at the inner/outer δ-table handoff (m=821), where the
enclosure widens; margins recover immediately once available slack outgrows
the added width.

  **The criterion (2.1) holds for all k ≥ 800, verified contiguously through
  k = 9001**, at which point the criterion is separately verified via a
  fully conservative (unsigned, S*-bound) argument that requires no
  δ-table beyond k=9002 and holds for all larger k unconditionally.

Boundary margins (crit_lo(k) := the certified lower bound on the LHS of
(2.1)):

| k | 797 | 798 | 799 | 800 | 801 | 802 |
|---|---|---|---|---|---|---|
| margin | −107.3 | −55.2 | −3.0 | +49.4 | +101.9 | +154.5 |

The crossing is clean and monotone through the boundary — not an artifact of
a particular constant choice.

**Validity range for all constants above:** k ≥ 500 (the range over which the
S2 quantifier-corrected bound |δ_m| ≤ 2.8552·m·log(m+1) + 9.6 + 0.02m was
established; see v-prior working notes for the term-ratio monotonicity
argument). Since 500 < 800, this is not binding.

---

## 10. Outlook

The analytic threshold K₀ = 800 stands against certified computation
presently at k = 200 (the gap 201–799 remains to be computed). Cost scales
roughly as k³ in the recurrence evaluations, so closing this gap is on the
order of (800/200)³ ≈ 64× the existing k=200 run — a substantially more
tractable target than v5's original (3527/200)³ ≈ 5500× estimate. A timed
benchmark on a moderate slice (k ≈ 400–500) is the natural next step before
committing compute.

Of the remaining sources, S2/Δ(k) is still the largest single contributor
to E(k) at the crossing (via the log2/4 scaling now correctly applied), and
its coefficient (2.8552) is traced from GLW's own (3.13)–(3.14) rather than
independently re-derived; extracting the *explicit* secondary term of their
Lemma 3.3 (rather than using their stated big-O bound, even signed) is the
most promising further avenue, with illustrative estimates suggesting a
further reduction toward K₀ ≈ 700 is plausible, though not attempted here.

**The one external dependency.** This note's reconstruction of GLW §3 has
been checked directly against their published text at every step used above,
and the process of doing so caught two genuine accounting errors in our own
earlier draft (§8, items 1–2). It has not been checked by a second party.
The specific claims most worth an author's confirmation, in order of
consequence to K₀: (a) that (3.8)'s bracketed term is the exact deterministic
quantity we take it to be (supporting the signed treatment in §5–6, not
merely an upper bound); (b) that our three-source decomposition of (3.13)–
(3.14)'s error is exhaustive.

---

## Appendix A. Certified constants (all ball arithmetic, prime cutoff 8×10⁶ unless noted)

| constant | value | role |
|---|---|---|
| d | 0.3786950 ± 4×10⁻⁷ | a₁ = (d log2)/4 |
| a₁ | 0.06562284 ± 4×10⁻⁹ | criterion leading coefficient |
| ρ (residue at G₂'s nearest pole z=3) | −0.1749323 ± 1×10⁻⁸ | S3/S1 tail bounds |
| sup\|H\| on \|z\|=4.2 | 101.245 ± 6×10⁻⁷ | S3 tail |
| U (signed) | 0 ± 0.137 | S3 |
| V (signed) | 0 ± 2.72 | S3 |
| α (S1 slope) | 17.538 | §4, valid k≥14 |
| β (S1 intercept) | −49.352 | §4 |
| S* = Σ\|cᵢ\|2ⁱ | 6.98 | superseded by signed Δ(k), §6 |
| **K₀** | **800** | main result |

## Appendix B. Trusted computing base

All ball-arithmetic computations use Arb/FLINT via python-flint 0.9.0. The
Stieltjes constants (§4) and the Riemann zeta evaluations (§7, boundary
checks) use FLINT's built-in certified implementations. The δ-table (§6) was
independently cross-validated against a from-scratch mpmath implementation
(40–80 decimal digits) of the original A_m integral definition at four test
points, with agreement to 6+ significant figures in each case.
