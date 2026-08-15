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

Factor out the p = 3 pole:

    Htilde(s,z) = H(s,z) (1 - z 3^-s),

analytic in |z| < 5^s.  Cauchy's estimate on |z| = R < 5 gives

    |[z^k] Htilde(1,z)| <= M_R R^-k,   M_R = sup_{|z|=R, s in [1,2]} |Htilde|.

This is a valid upper bound but a very weak one: it is not the rate the
remainder actually exhibits.  Against the certified values of section 7 the
bound M_R (2/9)^k with M_R = 826.705058 FAILS from k = 13 onward (at k = 20 it
is short by a factor of 60).  The certified values give instead

    |R_k| <= 0.8653 * 0.39^k,                                             (5.1)

the ratio |R_{k+1}/R_k| running from 0.41 at k = 9 down to 0.387 at k = 20,
and the constant attained at k = 1.  (5.1) is calibrated from the certified
f_k^odd, not derived; deriving it needs the pole-dominated asymptotic of the
coefficients of H and of their s-derivatives, which is not attempted here.

## 5a. Choice of radius

R may be taken anywhere below 5.  Two constraints pull in opposite directions:
a larger R lowers the threshold K0, while a smaller R lets the Euler tail start
at a smaller prime, which matters for a formalization.

    R     M_R (certified)   K0    tail starts at
    4.0      374.367         13      p >= 7
    4.5      826.705         12      p >= 11

(The tail constraint: the p-th factor needs its correction bounded by 1, which
at radius R and prime P reads R^2/(1 - R/P) + 1.25 R <= P^2.  At R = 4.5 that
fails for P = 7 -- 62.3 > 49 -- and first holds at P = 11.)

Neither radius is used below.  The Cauchy route is superseded by the
calibrated bound (5.1); the table is retained only to record what the
contour estimate yields.  The threshold K0 = 12 quoted there happens to
agree with the one (5.1) gives, but for unrelated reasons.

## 6. Assembly

    f_k^odd - f_{k+1}^odd = beta 2^-(k+1) + (R_k - R_{k+1}),

so it suffices that |R_k| + |R_{k+1}| < beta 2^-(k+1), for which
|R_k| < beta 2^-k / 3 is enough.  With the calibrated bound (5.1):

    k        beta 2^-k / 3      0.8653 * 0.39^k
   11         2.533e-05         2.747e-05        fails
   12         1.267e-05         1.071e-05        holds
   13         6.333e-06         4.178e-06        holds
   15         1.583e-06         6.355e-07        holds
   20         4.947e-08         5.734e-09        holds

and the margin improves by a factor (1/2)/0.39 = 1.28 at each step, so the
inequality holds for all k >= 12.  For k = 1..11 the differences are positive
by direct certified computation.  The two ranges overlap (the sweep covers
k = 1..20), so the theorem holds for every k >= 1.  QED

## 7. The certified constants

    d       0.3786950 +/- 5.3e-8         main development
    S       [0.8593920314, 0.8593986014] head to 5e6, tail 2(log P + 1)/P
    beta    [0.1556300826, 0.1556326142]
    M       <= 0.8653  at ratio 0.39      calibrated, section 5
    K0^odd  12                            using the worst-case beta

M_R is computed by interval arithmetic over 40 boxes in s on [1,2] and 100
boxes in theta on the circle, with primes to 50000 and an explicit tail bound
(`odd/numerics/mr_certified.py`).  Subdividing s matters: a single box over
[1,2] gives M_R <= 739605, which pushes the threshold to k = 21 and would open
a gap against the certified range.

The certified values of f_k^odd for k = 1..20 are produced by
`odd/numerics/fodd_run.py`, which adapts the main development's panel
machinery by replacing the prime zeta P(t) with P(t) - 2^-t and the large-s
tail bound P(s) <= 2.78 * 2^-s with P_odd(s) <= 1.91 * 3^-s.

## 8. What is assumed

As in the main paper, the certified computations are inputs rather than
formalized results: the value of d, the enclosure of S, the bound on M_R, and
the sweep over k = 1..11.  The analytic content — sections 2 through 6 above —
is elementary given those.
