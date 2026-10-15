# Certified computation of the Erdős sums f(ℕ_k) for k ≤ 200

**Methods note accompanying `certificate.json`** — draft, July 2026

## 1. Statement

For k ≥ 1 let ℕ_k = {n : Ω(n) = k} denote the k-almost primes and ℕ_k* its
squarefree subset. Following Erdős (1935) and Lichtman (arXiv:1909.00804,
arXiv:2303.08277), define

    f(ℕ_k) = Σ_{n ∈ ℕ_k} 1/(n log n),      f(ℕ_k*) analogously.

The computation certifies rigorous enclosures [lo_k, hi_k] ∋ f(ℕ_k) for
2 ≤ k ≤ KMAX and, as corollaries by interval comparison,

**Proposition.** f(ℕ_k) < f(ℕ_{k+1}) for 6 ≤ k < KMAX, and
f(ℕ_k*) > f(ℕ_{k+1}*) for 2 ≤ k < KMAX.

This closes the finite range needed to complement an explicit form of the
asymptotic f(ℕ_k) = 1 − (a + o(1)) k²/2^k of arXiv:2303.08277, whose
monotonicity conclusion holds for k sufficiently large.

## 2. Integral representation and algorithm

With P_k(s) = Σ_{Ω(n)=k} n^{−s} the k-almost-prime zeta function and
P = P_1 the prime zeta function, the identity 1/(n log n) = ∫_1^∞ n^{−s} ds
gives f(ℕ_k) = ∫_1^∞ P_k(s) ds. The integrand is computed by the recursion
(arXiv:1909.00804, §3)

    P_k(s) = (1/k) Σ_{j=1}^{k} P(js) P_{k−j}(s),

and, for the squarefree variant, the same recursion with the factor (−1)^{j+1}
on the j-th term. P(s) itself is evaluated by the Möbius series
P(s) = Σ_{m≥1} (μ(m)/m) log ζ(ms). The substitution s = 1 + e^{−u} maps the
mass of the integrand — which concentrates at s − 1 ≍ e^{−k} — to a smooth
bump near u ≈ k of width ≍ √k; the transformed integral over u ∈ [ULO, UHI]
is evaluated by composite Gauss–Legendre quadrature with NGL nodes per panel
of width H. All arithmetic is performed in Arb ball arithmetic (FLINT), so
every intermediate quantity is a rigorous enclosure. One recursion pass per
node yields P_1, …, P_KMAX simultaneously; the cost is per node, not per k.

## 3. Error accounting

Each reported enclosure includes six error sources.

**(A) Arithmetic.** Carried automatically by ball arithmetic at PREC bits.

**(B) Series truncation.** The Möbius series is truncated at the first m with
m·s > (PREC + 30)/log₂e-adjusted threshold; using 0 < log ζ(x) < 2^{1−x}
for x ≥ 2, the discarded tail is at most Σ_{m' > m} 2^{1−m's}/m' < 2^{2−ms},
added to the enclosure as a symmetric ball.

**(C) Quadrature discretization.** The transformed integrand
F(u) = P_k(1 + e^{−u}) e^{−u} is analytic on the strip |Im u| < π/2, since
Re s = 1 + e^{−Re u} cos(Im u) > 1 there and P_k is an absolutely convergent
Dirichlet series for Re s > 1. For each panel, mapped affinely to [−1, 1],
the n-point Gauss rule error is bounded via the Bernstein ellipse E_ρ with
semi-minor axis β = 2δ/H (δ = 1.45 < π/2), ρ = β + √(1+β²), using the bound
of Trefethen (Is Gauss quadrature better than Clenshaw--Curtis?, SIAM Rev.
50 (2008), 67--87, Thm 4.5 / eq. (4.14); = ATAP Thm 19.3):

    |I − I_n| ≤ (64/15) · M · ρ^{−2n} / (1 − ρ^{−2}),

where n is the NUMBER OF NODES.  The source states the exponent as ρ^{−(2n+2)}
with I_n built on n+1 nodes, which is the same thing.

applied with an additional factor 10 of safety and the interval-scaling
factor H/2, where M ≥ sup_{E_ρ} |F|. The sup is controlled by the termwise
bound |P_k(s)| ≤ P_k(Re s) and monotonicity of P_k on the reals:
M ≤ P_k(σ_min) · e^{−(a−ext)}, with σ_min = 1 + cos(δ) e^{−(b+ext)} and
ext = √((H/2)² + δ²) the ellipse's extent in Re u beyond the panel [a, b].
P_k(σ_min) is itself evaluated as a rigorous enclosure (upper endpoint used),
costing one extra recursion pass per panel.

**(D) Nodes and weights.** Gauss–Legendre nodes are certified by interval
Newton: from a refined midpoint x̂, the operator N(X) = x̂ − P_n(x̂)/P_n′(X)
is evaluated over an inflated ball X; verification N(X) ⊆ X proves the exact
node lies in N(X), which is then used (with the induced weight ball) in all
quadrature sums. The exact-node hypothesis of the bound in (C) is thereby
combined soundly with ball evaluation.

**(E) Tail at large s.** For s ≥ 2, P(s) ≤ 2^{−s} + Σ_{odd n≥3} n^{−s}
≤ 2^{−s}(1 + 16/9) < 2.78·2^{−s}, and P_k(s) ≤ P(s)^k termwise (each n with
Ω(n)=k is counted at least once in the k-fold product). Hence

    ∫_{S0}^∞ P_k(s) ds ≤ 2.78^k · 2^{−k S0} / (k log 2),   S0 = 1 + e^{−ULO}.

**(F) Tail at s → 1⁺.** By arXiv:1909.00804 Lemma 5.6, for 1 < s < 1+e^{−2k},
P_k(s) ≤ (1/k!) log(1/(s−1))^k. With the cut at u = UHI ≥ 2k + 2 (we take
UHI = 3.5·KMAX) and the elementary bound ∫_x^∞ u^k e^{−u} du ≤ 2 x^k e^{−x}
for x ≥ 2k,

    ∫_1^{1+e^{−UHI}} P_k(s) ds ≤ 2 · UHI^k · e^{−UHI} / k!.

Both tail bounds apply verbatim to the squarefree variant since
P_k*(s) ≤ P_k(s) termwise.

## 4. Scaling of the certification margin

The near-1 tail bound behaves like (3.5 e^{−2.5})^k ≈ 0.287^k in the worst
case k = KMAX, while the quantity being resolved, 1 − f(ℕ_k) ≍ a k²/2^k,
shrinks only like 0.5^k. The margin therefore widens with k: at k = 200 the
tail bound is ≈ 10^{−110} against a signal of ≈ 10^{−56}. Quadrature bounds
at the production parameters (H = 0.8, NGL = 52, δ = 1.45 ⇒ ρ ≈ 7.39,
ρ^{−104} ≈ 10^{−91}) are similarly negligible relative to the signal.

## 5. Validation

The pipeline reproduces all twenty-digit values of Figure 2 of
arXiv:1909.00804 (both f(ℕ_k) and f(ℕ_k*), k ≤ 10, independently computed
there in Mathematica and Pari/GP), the difference table of Figure 3
(k ≤ 20), and Cohen's 50-digit value of f(ℕ_1) to 21 digits (the remainder
attributable to the k = 1 large-s tail, which decays only as 2^{−s} and is
excluded from all certified claims). Enclosures are additionally stable
under independent changes of panel width, node count, and integration range.

## 6. Reproducibility

`certified.py KMAX PREC [p0 p1]` computes panels [p0, p1) and checkpoints
per-k partial sums; `certificate.py KMAX PREC` verifies full panel coverage,
adds tail balls, and emits `certificate.json` containing outward-rounded
decimal enclosures, per-pair certified monotonicity gaps, all parameters,
library versions, and a SHA-256 of the payload. The computation is
embarrassingly parallel over panels. Trusted computing base: FLINT/Arb.

## 7. Caveats

The quadrature constant is taken from Trefethen ATAP Thm 19.3 in a
conservative form with an additional 10× factor; the exact printed statement
should be verified before formal citation. Decimal enclosures in the
certificate are outward-rounded from binary balls and are therefore slightly
wider than the internal enclosures. The k = 1 row is excluded from certified
claims (its large-s tail is handled differently and is irrelevant to the
monotonicity range).
