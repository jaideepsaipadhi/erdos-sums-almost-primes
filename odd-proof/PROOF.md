# The odd Erdős sums are strictly decreasing

**Theorem.** Let

    f_k^odd = sum over odd n >= 3 with Omega(n) = k of 1/(n log n).

Then f_k^odd > f_{k+1}^odd for every k >= 1, and f_k^odd -> 1/2.

This is the companion to the main result of *The Erdős sums of almost primes
increase strictly from k = 6*, which shows the unrestricted sums f_k are
strictly **increasing** from k = 6, disproving Banks–Martin.  The two together
say that the failure of Banks–Martin is caused entirely by the prime 2.

---

## 1. Notation and the integral representation

For s > 1 put

    P_k^odd(s) = sum over odd n with Omega(n) = k of n^-s,

so that (by the same argument as Lemma 2.1 of the main paper, applied to the
odd n)

    f_k^odd = int_1^inf P_k^odd(s) ds.                                    (1.1)

The generating function is the Euler product over odd primes:

    sum_k P_k^odd(s) z^k = prod_{p >= 3} (1 - z p^-s)^-1.                 (1.2)

## 2. The decomposition

Write (1.2) as zeta(s)^z H(s,z), so that

    H(s,z) = (1 - 2^-s)^z prod_{p>=3} (1 - z p^-s)^-1 (1 - p^-s)^z.       (2.1)

**The key structural point.** H(s,·) is analytic in |z| < 3^s, because the
factor with the smallest pole is p = 3.  In the unrestricted problem the
corresponding function is analytic only in |z| < 2^s, so the evaluation point
z = 2 lies ON the boundary; here it lies strictly INSIDE.  This is the whole
reason the odd case is easier: on the boundary one picks up a k^2 factor
competing with 2^-k, which is what produces the turnaround at k = 6 and forces
the delta-table and criterion machinery of sections 4-7 of the main paper.
Inside, the leading behaviour is a constant times 2^-k with nothing to
compete with it.

Substituting u = log zeta(s) in (1.1) and expanding

    s - 1 = e^-u + gamma e^-2u + O(e^-3u),                                (2.2)

the contributions to f_k^odd organise by powers of e^-u.  Using
int_0^inf u^k e^-ju / k! du = j^-(k+1):

    order e^-u :   H(1,1)                                                 (2.3)
    order e^-2u:   2^-(k+1) [ d_s H(1,2) + 2 gamma H(1,2) ]               (2.4)
    order e^-ju:   O(j^-(k+1)),  j >= 3.                                  (2.5)

## 3. The limit

From (2.1) at z = s = 1 the product telescopes against zeta, leaving

    H(1,1) = 1 - 2^-1 = 1/2,

so by (2.3), f_k^odd -> 1/2.  Equivalently: the limit is the omitted Euler
factor evaluated at z = s = 1.  (For the unrestricted sums the same
computation gives 1.)

## 4. The leading term

At z = 2,

    H(1,2) = (1/4) prod_{p>=3} (1 - 1/p)^2 / (1 - 2/p) = 1/(4 C_2) = d,

the same constant d = 0.3786950 that appears in the main paper, and

    d_s log H(1,2) = 2 log 2 - 2S,    S = sum_{p>=3} log p / ((p-1)(p-2)).

Substituting into (2.4):

    f_k^odd = 1/2 + beta 2^-k + R_k,    beta = d (log 2 - S + gamma).      (4.1)

**Numerically** beta = 0.15563, and (4.1) is confirmed against the certified
values of f_k^odd: Richardson extrapolation of B(k) = 2^k (f_k^odd - 1/2) with
ratio 3/4 gives 0.157522, 0.156515, 0.156231 at k = 16, 18, 19, converging to
beta from above.

## 5. The remainder

Write

    R_k = f_k^odd - 1/2 - beta 2^-k

for the remainder after the two main terms of (4.1).  This section proves

    |R_k| <= C (k+3)^3 3^-k,   C = 4900,                                (5.1)

and hence, with section 6, the threshold K0^odd = 59.

The rate is 3^-k, not the 4.5^-k of a naive Cauchy estimate: the pole of
H(s,.) at z = 3^s sets it, and no contour argument does better.  The factor
(k+3)^3 comes from the second s-derivative, whose pole at z = 3^s has order
three.

### 5.1 Why the order expansion cannot be summed

Section 2 organises the integrand by powers of e^-u, with (2.5) recording the
order-m contribution as O(m^-(k+1)).  That expansion is ASYMPTOTIC, not
convergent, and must not be summed over m.

eps^r times the Jacobian contributes at order e^-(r+1)u, so the order-m term
draws on the (m-1)th s-derivative of the coefficients.  Those have a pole of
order m at z = 3^s, hence coefficients of size i^(m-1) 3^-i, and the order-m
contribution is

    m^-(k+1) sum_{i<=k} c_i^(m) m^i ~ [C_{m-1}/(m-1)!] k^(m-1) 3^-k/(m-3).

The power of k GROWS with m; summing over m >= 3 diverges.  Earlier drafts of
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

The "(lower order)" is made explicit here; earlier drafts left it unquantified.
It is three separate things, and only the second is large: (a) is smaller than
the main term by five to eight orders of magnitude over the range that matters,
(b) multiplies the leading term by CE/3 = 1.83 and is what moves the threshold,
and (c) is a cost of the split this note performs, not an omission in the
argument it formalizes.

(a) THE TWO COEFFICIENT TAILS.  The main terms of section 4 integrate to the
PARTIAL sums over j <= k, not to 1/2 and beta 2^-k; the differences
sum_{j>k} h_j(1) and 2^-(k+1) sum_{j>k} (b_j + 2 gamma h_j(1)) 2^j join R_k.
Both are bounded by the same pole-cancellation device as (5.4)-(5.5), but at
FIRST and SECOND order rather than third:
    S_0 := sum_i |a_i| 3^i,  a_i = [z^i] H(1,z)(1 - z/3),        S_0 <= 44.5987
    S_1 := sum_i |g1_i| 3^i, g1_i = [z^i] (d_s H)(1,z)(1-z/3)^2, S_1 <= 486.1945
Note the second tail's coefficient family is B(z) = d_s H_o(1,z) + 2 gamma
H_o(1,z), not d_s H_o alone, so its weighted norm is S_1 + 4 gamma S_0 = 589.17
(< 590) rather than S_1.  Lemma (i) then gives |h_j(1)| <= S_0 3^-j and (ii)
gives |B_j| <= 590 (j+1) 3^-j, and since
    sum_{j>k} (j+1)(2/3)^j = 3(k+4)(2/3)^(k+1),
the two tails contribute S_0/2 and 5*590/64 = 46.09 to the constant of (5.1),
using (k+4)/(k+3)^3 <= 5/64 for k >= 1.  (An earlier draft used 9 S_1/128 =
34.19 here, which omitted the 2 gamma h_j(1) part.)  (s0_recursion.py, s0_cauchy.py,
s1_recursion.py, s1_cauchy.py.)

(b) THE JACOBIAN AND PRODUCT ERRORS.  (5.3) bounds only the Lagrange remainder
R_j J.  The split of the integrand also leaves
    h_j(1) (J - e^-u - 2 gamma e^-2u)   and   b_j (eps J - e^-2u),
each O(e^-3u) but with its own constant.  Writing CJ, CP, Cb, Cf for the four
constants of those expansions and CE = CJ + CP + Cb^2 (Cf+1), the coefficient
of (5.3) is CE/3 times, not 1 times, sum_{j<=k}|h_j''|3^j.  Over the range
s in (1, sOf(3)] that the split requires, CE <= 5.48910 (ce_taylor.py; the
log prints 5.4890962927).

(c) THE NEAR REGION.  This one is not a gap in the argument but a cost of
making it rigorous: the expansions in (b) are asymptotic, valid only for
u >= U, and the original treats them as holding throughout.  This note uses
U = 3 and bounds 0 < u <= U separately.  On 0 < u <= U the integrand is bounded directly,
contributing CN <= 367.8435 (cn_certified.py) from the coefficient sum itself and
NEARU <= 26.0962 (nearu_certified.py) from the two main terms.

### 5.2 The coefficient sum

Factor out the pole:

    G_2(s,z) = d_s^2 H(s,z) (1 - z 3^-s)^3,                                (5.4)

analytic in |z| < 5^s.  With g_j = [z^j] G_2(1,z), expanding (1 - z/3)^-3 by
the negative binomial series gives

    h_j'' = 3^-j sum_{i<=j} g_i 3^i C(j-i+2, 2),

and summing over j <= k,

    sum_{j<=k} |h_j''| 3^j <= C(k+3, 3) * S,   S := sum_i |g_i| 3^i.       (5.5)

Since C(k+3,3) <= (k+3)^3/6, (5.3) and (5.5) give the LAGRANGE-REMAINDER part
of (5.1) with coefficient CE S/18 (the CE of 5.1(b); with CE = 3 this would be
the S/6 of earlier drafts).  Adding 5.1(a) and 5.1(c),
    C = CE S/18 + S_0/2 + 5*590/64 + CN + NEARU
      = 4395.5 + 22.3 + 46.1 + 367.8 + 26.1 = 4857.9,
and (5.1) holds with C = 4900.

A bound |h_j''| <= C 3^-j would be exactly critical -- sums like
sum_{j<=k} |h_j''| 3^j would then grow linearly in k rather than converge.  It
is the pole cancellation in (5.4) that makes S finite.

### 5.3 Computing S

S is split at i = 16.

HEAD, i <= 16, by direct interval recursion (odd-proof/numerics/hcoeff_recursion.py).
Writing

    log H(s,z) = z L_1(s) + sum_{j>=2} z^j L_j(s),
      L_1 = log(1-2^-s) + sum_{p>=3}[p^-s + log(1-p^-s)],
      L_j = P(s,j)/j,  P(s,j) = sum_{p>=3} p^-sj,

the coefficients of H follow from h_m = (1/m) sum_{j<=m} j L_j h_{m-j}, those
of d_s^2 H from d_s^2 H = H (D_1^2 + D_2) with D_r = sum_j L_j^(r) z^j, and the
g_i from the product with (1 - z/3)^3.  Every step carries s as a certified
interval, [1,2] partitioned into 1600 boxes.  Result:

    sum_{i<=16} |g_i| 3^i <= 8424.

TAIL, i > 16, by Cauchy, which is cheap here because the terms are small.  By
(5.4) G_2 is analytic in |z| < 5, so on |z| = R = 4.5, |g_i| <= M R^-i with
M = sup_{|z|=R, s in [1,2]} |G_2| <= 1.97e6 (odd-proof/numerics/mr_deriv_sweep.py),
giving

    sum_{i>16} |g_i| 3^i <= M (3/R)^17/(1 - 3/R) <= 5990.

Hence S <= 14414.  This is the S of 5.2; the constant C of (5.1) is
CE S/18 + S_0/2 + 5*590/64 + CN + NEARU = 4857.9, not S/6 -- see 5.2.

BOTH HALVES ARE NECESSARY.  Cauchy from i = 0 gives C = 327869 and K0 = 71,
too weak to meet the certified sweep: the circle estimate discards the
cancellation among the true coefficients, costing about 5.5e5.  The recursion
alone cannot reach large i: interval width in s compounds through the
recurrence, and past i ~ 14 the computed |g_i| 3^i stop decreasing and rise,
which is width rather than signal.

### 5.4 What is assumed

(5.1) rests on the interval computations

  * sum_{i<=16} |g_i| 3^i <= 8424        (1600 s-boxes, primes to 1e5)
  * sup_{|z|=4.5, s in [1,2]} |G_2| <= 1.97e6   (200 theta x 40 s boxes)
  * S_0 <= 44.5987                       s0_recursion.py + s0_cauchy.py
  * S_1 <= 486.1945                      s1_recursion.py + s1_cauchy.py
  * CN  <= 367.8435                      cn_certified.py  (recursion + Cauchy)
  * NEARU <= 26.0962                     nearu_certified.py (head + envelope)
  * CE  <= 5.48910                       ce_taylor.py  (log: 5.4890962927)

and on 5.1-5.2, elementary given them.  No constant is fitted to the certified
f_k^odd; the agreement with those values is a check, not an input.

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

    f_k^odd - f_{k+1}^odd = beta 2^-(k+1) + (R_k - R_{k+1}),

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
computation, which reaches k = 60 (odd-proof/numerics/fodd60.log).  The ranges
overlap at 59, 60, so the theorem holds for every k >= 1.  QED

With the C = 2402.3 of earlier drafts the first success was k = 57; the
corrected C moves it to 59.  The certified sweep to 60 still covers the gap,
but the margin is two values rather than four.

## 7. The certified constants

    d           0.3786950 +/- 5.3e-8         main development
    S_odd       [0.8593920314, 0.8593986014]  head to 5e6, tail 2(log P + 1)/P
    beta        [0.1556300826, 0.1556326142]
    sum|g_i|3^i <= 8424  (i <= 16)            hcoeff_recursion.py, 1600 s-boxes
    sup|G_2|    <= 1.97e6 on |z|=4.5          mr_deriv_sweep.py
    S_0         <= 44.5987                    s0_recursion.py, s0_cauchy.py
    S_1         <= 486.1945                   s1_recursion.py, s1_cauchy.py
    S_1+4gS_0   <= 590                        the tail's coefficient family
    CN          <= 367.8435                   cn_certified.py
    NEARU       <= 26.0962                    nearu_certified.py
    CE          <= 5.48910                    ce_taylor.py
    C           4900                          (5.1), see 5.2
    K0^odd      59                            certified sweep reaches 60

The certified values of f_k^odd for k = 1..60 are produced by
odd-proof/numerics/fodd_run.py at 1000-bit precision, which adapts the main
development's panel machinery by replacing the prime zeta P(t) with P(t)-2^-t
and the large-s tail bound P(s) <= 2.78*2^-s with P_odd(s) <= 1.91*3^-s.

## 8. What is assumed

As in the main paper, the certified computations are inputs rather than
formalized results: the value of d, the enclosure of S, the bound on M_R, and
the sweep over k = 1..60.  The analytic content — sections 2 through 6 above —
is elementary given those.
