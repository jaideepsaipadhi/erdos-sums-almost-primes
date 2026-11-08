# The odd Erdős sums are strictly decreasing

**Theorem.** Let

    g_k = sum over odd n >= 3 with Omega(n) = k of 1/(n log n).

Then g_k > g_{k+1} for every k >= 1, and g_k -> 1/2.

This is the companion to the main result of *Monotonicity of Erdős sums*,
which shows the unrestricted sums f_k are strictly increasing from k = 6,
disproving Banks–Martin.  The two together
say that the failure of Banks–Martin is caused entirely by the prime 2.

---

## 1. Notation and the integral representation

For s > 1 put

    P_k^odd(s) = sum over odd n with Omega(n) = k of n^-s,

so that (by the same argument as Lemma 2.1 of the main paper, applied to the
odd n)

    g_k = int_1^inf P_k^odd(s) ds.                                    (1.1)

The generating function is the Euler product over odd primes:

    sum_k P_k^odd(s) z^k = prod_{p >= 3} (1 - z p^-s)^-1.                 (1.2)

## 2. The decomposition

Write (1.2) as zeta(s)^z H(s,z), so that

    H(s,z) = (1 - 2^-s)^z prod_{p>=3} (1 - z p^-s)^-1 (1 - p^-s)^z.       (2.1)

H(s,·) is analytic in |z| < 3^s, since the nearest pole comes from p = 3.
For the unrestricted product the radius is 2^s, so the evaluation point z = 2
lies on the first singular circle; here it lies strictly inside it.  On the
boundary the evaluation acquires a factor k^2 against 2^-k, which turns the
unrestricted sequence around at k = 6 and forces the delta-table and criterion
machinery of sections 4-7 of the main paper.  Inside, the leading term is a
constant times 2^-k.

Substituting u = log zeta(s) in (1.1) and expanding

    s - 1 = e^-u + gamma e^-2u + O(e^-3u),                                (2.2)

the contributions to g_k organise by powers of e^-u.  Using
int_0^inf u^k e^-ju / k! du = j^-(k+1):

    order e^-u :   H(1,1)                                                 (2.3)
    order e^-2u:   2^-(k+1) [ d_s H(1,2) + 2 gamma H(1,2) ]               (2.4)
    order e^-ju:   O(j^-(k+1)),  j >= 3.                                  (2.5)

## 3. The limit

From (2.1) at z = s = 1 the product telescopes against zeta, leaving

    H(1,1) = 1 - 2^-1 = 1/2,

so by (2.3), g_k -> 1/2.  Equivalently: the limit is the omitted Euler
factor evaluated at z = s = 1.  (For the unrestricted sums the same
computation gives 1.)

## 4. The leading term

At z = 2,

    H(1,2) = (1/4) prod_{p>=3} (1 - 1/p)^2 / (1 - 2/p) = 1/(4 C_2) = d,

the same constant d = 0.3786950 that appears in the main paper, and

    d_s log H(1,2) = 2 log 2 - 2S,    S = sum_{p>=3} log p / ((p-1)(p-2)).

Substituting into (2.4):

    g_k = 1/2 + beta 2^-k + R_k,    beta = d (log 2 - S + gamma).      (4.1)

Numerically beta = 0.15563, and (4.1) is confirmed against the certified
values of g_k: Richardson extrapolation of B(k) = 2^k (g_k - 1/2) with
ratio 3/4 gives 0.157522, 0.156515, 0.156231 at k = 16, 18, 19, converging to
beta from above.

## 5. The remainder

Write

    R_k = g_k - 1/2 - beta 2^-k

for the remainder after the two main terms of (4.1).  This section proves

    |R_k| <= C (k+3)^3 3^-k,   C = 4900,   for k >= 59,                 (5.1)

and hence, with section 6, the threshold K0^odd = 59.

The range in (5.1) is necessary, not conservative; see 5.1(c) below.  It costs
nothing, since (5.1) is used only for k >= K0^odd = 59 and monotonicity for
k <= 74 comes from the certified sweep, which does not call on it.

The rate is 3^-k, not the 4.5^-k of a naive Cauchy estimate: the pole of
H(s,.) at z = 3^s sets it, and no contour argument does better.  The factor
(k+3)^3 comes from the second s-derivative, whose pole at z = 3^s has order
three.

### 5.1 Why the order expansion cannot be summed

Section 2 organises the integrand by powers of e^-u, with (2.5) recording the
order-m contribution as O(m^-(k+1)).  That expansion is asymptotic, not
convergent, and must not be summed over m.

eps^r times the Jacobian contributes at order e^-(r+1)u, so the order-m term
draws on the (m-1)th s-derivative of the coefficients.  Those have a pole of
order m at z = 3^s, hence coefficients of size i^(m-1) 3^-i, and the order-m
contribution is

    m^-(k+1) sum_{i<=k} c_i^(m) m^i ~ [C_{m-1}/(m-1)!] k^(m-1) 3^-k/(m-3).

The power of k grows with m; summing over m >= 3 diverges.  Earlier drafts of
this note summed it, and the bound they reported -- M_R (2/9)^k with
M_R = 826.705058 -- is numerically false, failing from k = 13 onward against
the certified values of section 7.

The correct route truncates with an explicit remainder.  Taylor to second
order in Lagrange form,

    |h_j(s) - h_j(1) - (s-1) b_j| <= (1/2) sup_{t in [1,2]} |h_j''(t)| (s-1)^2,
                                                                         (5.2)

leaves one error term.  Since eps(u) ~ e^-u and the Jacobian ~ e^-u that term
is O(e^-3u), and int_0^inf u^m e^-3u/m! du = 3^-(m+1) gives, with m = k-j,

    |R_k| <= (1/3) 3^-k sum_{j<=k} |h_j''| 3^j + (lower order).            (5.3)

LEMMA (pole-coefficient bounds).  Let A(z) be analytic on |z| < 5 with
(1-z/3)^r A(z) = sum_m w_m z^m and W := sum_m 3^m |w_m| < infinity.  Then the
coefficients a_j = [z^j] A(z) satisfy
    |a_j| <= W 3^-j C(j+r-1, r-1),
so |a_j| <= W 3^-j for r = 1, (j+1) W 3^-j for r = 2, and C(j+2,2) W 3^-j for
r = 3.  Expanding (1-z/3)^-r by the negative binomial series gives
a_j = 3^-j sum_{m<=j} 3^m w_m C(j-m+r-1, r-1), and bounding the binomial by
C(j+r-1, r-1) termwise gives the claim.  (5.4)-(5.5) below is the case r = 3.

The "(lower order)" is made explicit here; earlier drafts left it unquantified.
It is three separate things, and only the second is large: (a) is smaller than
the main term by five to eight orders of magnitude over the range that matters,
(b) multiplies the leading term by CE/3 = 1.83 and is what moves the threshold,
and (c) is a cost of the split this note performs, not an omission in the
argument it formalizes.

(a) The two coefficient tails.  The main terms of section 4 integrate to the
partial sums over j <= k, not to 1/2 and beta 2^-k; the differences
sum_{j>k} h_j(1) and 2^-(k+1) sum_{j>k} b_j 2^j join R_k, where
b_j = h_j'(1) + 2 gamma h_j(1) ALREADY contains the 2 gamma h_j(1) term --
writing (b_j + 2 gamma h_j(1)) here, as an earlier version did, double-counts
it and contradicts the identification B(z) = d_s H_o + 2 gamma H_o = sum b_j
z^j two lines below.  The manuscript's eq:Rk-def has the correct sum.
Both are bounded by the same pole-cancellation device as (5.4)-(5.5), but at
first and second order rather than third:
(The paper writes Sigma_0, Sigma_1, Sigma_2 for S_0, S_1 and the S of 5.2,
indexing the three constants by pole order; the Lean parameter is S.)

    S_0 := sum_i |a_i| 3^i,  a_i = [z^i] H(1,z)(1 - z/3),        S_0 <= 44.5987
    S_1 := sum_i |g1_i| 3^i, g1_i = [z^i] (d_s H)(1,z)(1-z/3)^2, S_1 <= 486.1946
Note the second tail's coefficient family is B(z) = d_s H_o(1,z) + 2 gamma
H_o(1,z), not d_s H_o alone, so its weighted norm is S_1 + 4 gamma S_0 = 589.17
(< 590) rather than S_1.  The lemma at r = 1 gives |h_j(1)| <= S_0 3^-j, and at
r = 2 gives |B_j| <= 590 (j+1) 3^-j, and since
    sum_{j>k} (j+1)(2/3)^j = 3(k+4)(2/3)^(k+1),
the two tails contribute S_0/2 and 5*590/64 = 46.09 to the constant of (5.1),
using (k+4)/(k+3)^3 <= 5/64 for k >= 1.  (An earlier draft used 9 S_1/128 =
34.19 here, which omitted the 2 gamma h_j(1) part.)  (s0_recursion.py, s0_cauchy.py,
s1_recursion.py, s1_cauchy.py.)

(b) The Jacobian and product errors.  (5.3) bounds only the Lagrange remainder
R_j J.  The split of the integrand also leaves
    h_j(1) (J - e^-u - 2 gamma e^-2u)   and   b_j (eps J - e^-2u),
each O(e^-3u) but with its own constant.  Writing CJ, CP, Cb, Cf for the four
constants of those expansions and CE = CJ + CP + Cb^2 (Cf+1), the coefficient
of (5.3) is CE/3 times, not 1 times, sum_{j<=k}|h_j''|3^j.  Over the range
s in (1, sOf(3)] that the split requires, CE <= 5.48910 (ce_taylor.py; the
log prints 5.4890962927).

(c) The near region.  This one is not a gap in the argument but a cost of
making it rigorous: the expansions in (b) are asymptotic, valid only for
u >= U, and the original treats them as holding throughout.  This note uses
U = 3 and bounds 0 < u <= U separately.  On 0 < u <= U the two groups are
bounded separately: NEARU <= 26.0962 (nearu_certified.py) covers the two
subtracted main terms, and CN <= 367.8436 (cn_certified.py) covers the true
integrand.

CN does NOT cover the true integrand as stated, and this is where the range in
(5.1) comes from.  What has to be bounded is a sum of ABSOLUTE values,

    sum_{j<=k} int_0^3 u^{k-j}/(k-j)! |h_j(s(u))| J(u) du,

whereas cn_certified.py bounds the SIGNED coefficient identity
sum_j u^{k-j}/(k-j)! h_j(s(u)) = P_k^odd(s(u)).  That identity bounds the
absolute sum only if h_j >= 0, and the h_j alternate:

    h_1(s) = Pi(s) - log zeta(s) = log(1 - 2^-s) - sum_{m>=2} Pi(ms)/m < 0

for every s, with 1, -0.762, +0.377, -0.126, ... at s = sOf(3).

nearabs_certified.py repairs this.  |h_j| <= [z^j] H^+ where
H^+ = H exp(-2 h_1 z) has non-negative coefficients, so the sum is at most
P_k^+(s) = sum_i P^odd_{k-i}(s) a(s)^i/i! with a = 2|h_1|.  Every factor is a
Dirichlet series with positive terms, so P_k^+ decreases in s and a
left-endpoint Riemann sum bounds the integral with no quadrature error to
estimate; the s-tail closes as P_k^+(s_N)/(k log 2) because 3^-x <= 2^-x makes
every term decay by at least 2^-kt, and the k-tail uses Cauchy at R = 3.15,
just under 3^sOf(3) = 3.17383.  The result, over EVERY k in [59, 200] and not a
sample, is 3^k T_k <= 34.14, and <= 9.66 beyond 200 -- so CN = 367.8436 covers
the absolute sum too on k >= 59, with better than tenfold slack, and the ledger
above is unchanged.

Below k = 59 it does not.  Run with K0 = 1 (the settings of record otherwise:
`nearabs_certified.py 60 8.0 220 60 60 400 1`), the certified integral bound
peaks at 699.87 at k = 14 and exceeds CN = 367.8436 for exactly 9 <= k <= 25
(k=25 gives 369.96, k=26 gives 343.51).  So k >= 26 would in fact serve, and
59 is stated only because it is the only range in which (5.1) is ever applied.

An earlier version of this paragraph said "3^k T_k peaks at 15329 near k = 12
and only falls under CN at k = 24", and that a single all-k constant would be
"about 19819, which would move K0 to 63".  Both figures are WRONG HERE.
15329 is absratio.py's POINTWISE sum 3^k A_k(s(3)) at k = 12 (absratio.log:
15328.840), a different quantity from the integral that
eq:odd-nearabs-certified bounds, and "falls under CN at k = 24" is likewise
absratio's pointwise crossing.  19819 has no artifact at all.  And the
consequence does not follow: with an all-k constant near 700 in place of
367.84 the ledger becomes about 5190 and q(59) = 0.918*5190/4900 = 0.973 < 1,
so K0 would stay at 59.  Quote the figures above, from the integral run, and
do not reuse the pointwise ones.

The bridge from the pointwise bound to the integral is an analytic step that
neither this note nor the manuscript used to state.  It is short.  By
(1.1) and s = s(u),

    sum_{j<=k} int_0^3 (u^(k-j)/(k-j)!) h_j(s(u)) J(u) du
      = int_{s(3)}^inf P_k^odd(s) ds,

and every odd n with Omega(n) = k has n >= 3^k, so for s >= s(3)

    P_k^odd(s) = sum n^-s(3) n^-(s-s(3)) <= 3^(-k(s-s(3))) P_k^odd(s(3)),

whence int_{s(3)}^inf P_k^odd <= P_k^odd(s(3))/(k log 3) <= CN 3^-k/(k log 3),
comfortably inside the CN (k+3)^3 3^-k budget (at k = 1 it is 334.8 against
23542).  The manuscript now carries this as (4.19).

### 5.2 The coefficient sum

Factor out the pole:

    G_2(s,z) = d_s^2 H(s,z) (1 - z 3^-s)^3,                                (5.4)

analytic in |z| < 5^s.  With w_j = [z^j] G_2(1,z), expanding (1 - z/3)^-3 by
the negative binomial series gives

    h_j'' = 3^-j sum_{i<=j} w_i 3^i C(j-i+2, 2),

and summing over j <= k,

    sum_{j<=k} |h_j''| 3^j <= C(k+3, 3) * S,   S := sum_i |w_i| 3^i.       (5.5)

Since C(k+3,3) <= (k+3)^3/6, (5.3) and (5.5) give the Lagrange-remainder part
of (5.1) with coefficient CE S/18 (the CE of 5.1(b); with CE = 3 this would be
the S/6 of earlier drafts).  Adding 5.1(a) and 5.1(c),
    C = CE S/18 + S_0/2 + 5*590/64 + CN + NEARU
      = 4395.55 + 22.30 + 46.10 + 367.85 + 26.10 = 4857.90,
and (5.1) holds with C = 4900 on k >= 59.

The 0.9% of margin reflects the NS = 1600 box width, not the method.  Halving
it (odd-proof/numerics/hcoeff3200.log) gives head 7890.6 in place of 8423.9,
hence S <= 13881 and C = 4695.2, i.e. 4.2% of margin; the head is still
falling there.  K0 = 59 at either value and MR <= 4900 holds a fortiori, so
this section stays stated at NS = 1600 and the finer run is headroom only.

A bound |h_j''| <= C 3^-j would be exactly critical -- sums like
sum_{j<=k} |h_j''| 3^j would then grow linearly in k rather than converge.  It
is the pole cancellation in (5.4) that makes S finite.

### 5.3 Computing S

S is split at i = 16.

Head, i <= 16, by direct interval recursion (odd-proof/numerics/hcoeff_recursion.py).
Writing

    log H(s,z) = z L_1(s) + sum_{j>=2} z^j L_j(s),
      L_1 = log(1-2^-s) + sum_{p>=3}[p^-s + log(1-p^-s)],
      L_j = P(s,j)/j,  P(s,j) = sum_{p>=3} p^-sj,

the coefficients of H follow from h_m = (1/m) sum_{j<=m} j L_j h_{m-j}, those
of d_s^2 H from d_s^2 H = H (D_1^2 + D_2) with D_r = sum_j L_j^(r) z^j, and the
w_i from the product with (1 - z/3)^3.  Every step carries s as a certified
interval, [1,2] partitioned into 1600 boxes.  Result:

    sum_{i<=16} |w_i| 3^i <= 8424.

Tail, i > 16, by Cauchy, which is cheap here because the terms are small.  By
(5.4) G_2 is analytic in |z| < 5, so on |z| = R = 4.5, |w_i| <= M R^-i with
M = sup_{|z|=R, s in [1,2]} |G_2| <= 1.97e6 (odd-proof/numerics/mr_deriv_sweep.py),
giving

    sum_{i>16} |w_i| 3^i <= M (3/R)^17/(1 - 3/R) <= 5990.

Hence S <= 14414.  This is the S of 5.2; the constant C of (5.1) is
CE S/18 + S_0/2 + 5*590/64 + CN + NEARU = 4857.90, not S/6 -- see 5.2.

Both halves are necessary.  Cauchy from i = 0 gives C = 327869 and K0 = 71,
too weak to meet the certified sweep: the circle estimate discards the
cancellation among the true coefficients, costing about 5.5e5.  The recursion
alone cannot reach large i: interval width in s compounds through the
recurrence, and past i ~ 14 the computed |w_i| 3^i stop decreasing and rise,
which is width rather than signal.

### 5.4 What is assumed

(5.1) rests on the interval computations

  * sum_{i<=16} |w_i| 3^i <= 8424        (1600 s-boxes, primes to 1e5)
  * sup_{|z|=4.5, s in [1,2]} |G_2| <= 1.97e6   (200 theta x 40 s boxes)
  * S_0 <= 44.5987                       s0_recursion.py + s0_cauchy.py
  * S_1 <= 486.1946                      s1_recursion.py + s1_cauchy.py
  * CN  <= 367.8436                      cn_certified.py  (recursion + Cauchy)
  * 3^k T_k <= 34.14  (k >= 59)          nearabs_certified.py (absolute sum;
                                         what the near range actually needs)
  * NEARU <= 26.0962                     nearu_certified.py (head + envelope)
  * CE  <= 5.48910                       ce_taylor.py  (log: 5.4890962927)

and on 5.1-5.2, elementary given them.  No constant is fitted to the certified
g_k; the agreement with those values is a check, not an input.

All five of the new constants are arb enclosures end to end, with no
floating-point or mpmath step anywhere in the chain.  Two of them needed a
change of method to get there, and both failures are worth recording because
the naive route produces plausible numbers rather than obvious errors.

CE is certified over the whole range s in (1, sOf(3)], not at a sample of
points.  The four constants behind it are ratios in which zeta's pole at s = 1
cancels, so evaluating them on boxes of s loses the cancellation and the
enclosures diverge however narrow the boxes are taken -- five successive
approaches failed this way.  Expanding zeta as an arb power series about
1 + E/2 makes the cancellation symbolic, and the resulting series, whose
coefficients decay by a factor of ten per order, evaluate tightly on the whole
disc at once.

CN needs the prime sums P(t) = sum_{p>=3} p^-t for t = s, 2s, ..., 200s.
Enumerating primes to a cutoff and bounding the remainder does not work here:
at s ~ 1.05 the series converges so slowly that even a cutoff of 1e8 with the
Rosser-Schoenfeld bound leaves a factor of two, and compounding that through
200 recurrence steps inflated CN from 368 to 3820 -- enough to push K0 past
the certified sweep.  The Moebius series P(t) = sum_n mu(n)/n log zeta(nt)
avoids primes altogether and is exact to full precision.  The recurrence also
loses about a digit every 2.3 steps to cancellation, so it is run at 600 bits;
1200 bits gives the same head to every printed digit.

## 6. Assembly

    g_k - g_{k+1} = beta 2^-(k+1) + (R_k - R_{k+1}),

so it suffices that |R_k| + |R_{k+1}| < beta 2^-(k+1), for which
|R_k| < beta 2^-k / 3 is enough.  With (5.1):

    k        beta 2^-k / 3      C (k+3)^3 3^-k
   57         3.600e-19          6.328e-19       fails
   58         1.800e-19          2.217e-19       fails
   59         8.999e-20          7.759e-20       holds
   60         4.500e-20          2.713e-20       holds

T/P = C(k+3)^3 (2/3)^k is antitone in k (the ratio is ((k+4)/(k+3))^3 (2/3),
below 1 for k >= 4), with value 0.0476 at k = 59, so the inequality holds for
all k >= 59.  For k = 1..58 the differences are positive by direct certified
computation, which reaches k = 75 (odd-proof/numerics/fodd75.log).  The ranges
overlap on 59..75, so the theorem holds for every k >= 1.  QED

With the C = 2402.3 of earlier drafts the first success was k = 57; the
corrected C moves it to 59.  The certified sweep to 60 still covers the gap,
and the sweep to 75 leaves sixteen values of overlap.

## 7. The certified constants

    d           0.3786950 +/- 5.3e-8         main development
    S_odd       [0.8593920314, 0.8593986014]  head to 5e6, tail 2(log P + 1)/P
    beta        [0.1556300826, 0.1556326142]
    sum|w_i|3^i <= 8424  (i <= 16)            hcoeff_recursion.py, 1600 s-boxes
    sup|G_2|    <= 1.97e6 on |z|=4.5          mr_deriv_sweep.py
    S_0         <= 44.5987                    s0_recursion.py, s0_cauchy.py
    S_1         <= 486.1946                   s1_recursion.py, s1_cauchy.py
    S_1+4gS_0   <= 590                        the tail's coefficient family
    CN          <= 367.8436                   cn_certified.py
    3^k T_k     <= 34.14    (k >= 59)         nearabs_certified.py
    NEARU       <= 26.0962                    nearu_certified.py
    CE          <= 5.48910                    ce_taylor.py
    C           4900                          (5.1), see 5.2
    K0^odd      59                            certified sweep reaches 75

The certified values of g_k for k = 1..75 are produced by
odd-proof/numerics/fodd_run.py at 1000-bit precision, which adapts the main
development's panel machinery by replacing the prime zeta P(t) with P(t)-2^-t
and the large-s tail bound P(s) <= 2.78*2^-s with P_odd(s) <= 1.91*3^-s.

## 8. What is assumed

As in the main paper, the certified computations are inputs rather than
formalized results: the value of d, the enclosure of S, the bound on M_R, and
the sweep over k = 1..75.  The analytic content — sections 2 through 6 above —
is elementary given those.
