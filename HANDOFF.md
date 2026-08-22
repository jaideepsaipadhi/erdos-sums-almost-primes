# Development log

A chronological record of the formalization, kept for the design decisions and
the Lean-specific lessons.  The early entries are working notes and describe
targets that have since been met; the "=== COMPLETE ===" section below is the
accurate final statement for the main theorem, and "=== ODD CASE ===" for the
companion.


MANUSCRIPT RECEIVED (banks-martin-proof.pdf, in repo /docs if committed): the
complete spec. FORMALIZATION ROADMAP (three tiers):
T1 (target, closes manuscript Caveat 8.1a): formalize the six pages of human
   proofs — Lem 2.1 (= lemma1_foundation, DONE), eq (2) (= criterion, DONE),
   Lem 2.2 exact expansion, Lem 2.4 exactness I'_k = sum c_i 2^{i-k} A_{k-i},
   Prop 2.5 assembly identity (6), Thm 4.1 two-sided delta bound, Thm 6.1
   refined E1 enclosure, Thm 7.1 far range k>=2440.
T2 (the wall inside T1): Thm 4.1 needs gap-5 integral identity + Euler's
   gamma = -int e^{-u} log u du. CHECK MATHLIB FIRST: Real.Gamma deriv at 1,
   exponential integral. Mitigation: only the UPPER delta bound is needed and
   aE1(a) <= e^{-a} may be provable from the defining integral directly.
T3 (do NOT formalize): Arb computations (delta-table, prime tails, box sweeps,
   arc sups) stay as NumericalFacts hypothesis = trusted computing base, per
   manuscript Caveat 1.3b. dConst, rhoConst now genuinely defined; still to
   define as real objects: SstarConst (sum 2^i |c_i| — needs c_i := taylor
   coeff of G2(1,z), i.e. formalize G2 first), alphaConst, GammaConst (deriv
   sups). Defining G2 and c_i in Lean is the natural session opener — it
   unlocks Lem 2.2/2.4/Prop 2.5 statements simultaneously.
END STATE: Lean-verified reduction + Arb-certified hypothesis = machine-checked
conditional theorem, trust surface = FLINT/Arb only.

SESSION 2 (2026-07-25 evening): Tier 1 foundation poured, all green:
- Def 2.3 objects (Sm/Am/deltaM) + anchors (delta_0 = -1 proven)
- Gamma evaluation integral_exp_neg_mul_pow; Jint defined
- Substitution keystone: subst_image, subst_injOn, integral_Ioc_subst
  (integral_image_eq_integral_abs_deriv_smul works in pin)
- MANUSCRIPT EQ (5) MACHINE-VERIFIED: Am_eq_sum_Jint
- Bfun + Bfun_nonneg, betaCirc, integral_pow_exp_neg_two_mul
- Integrability: integrable_pow_exp (via Real.GammaIntegral_convergent),
  integrable_pow_exp_two, integrable_Jint_integrand
NEXT SESSION OPENER: the J-split — J(i) as Jint via integral_add over the
three pieces (betaCirc part + Gamma part - log2-weighted scaled part), then
identity (11) as Finset algebra over Am_eq_sum_Jint, then Thm 4.1 LOWER bound
(needs only Bfun_nonneg + the split). Upper bound = the gap-5/gamma wall,
digamma_one available; still needs Gamma differentiation under integral.
PIN LESSONS TONIGHT: inside setIntegral_congr_fun bodies use simp only never
rw (lambda-blindness); every ring after field_simp is try ring; ae arguments
via filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu.

EULERGAMMA SCAFFOLD (Banksmartin/EulerGamma.lean, separate file to preserve
Basic.lean's 1-sorry invariant). 7 obligations stated and typechecked; 3 and 5
PROVEN. Key pin finds: Real.hasDerivAt_Gamma_one : HasDerivAt Gamma (-gamma) 1
and Real.eulerMascheroniConstant_eq_neg_deriv both live in
Mathlib/NumberTheory/Harmonic/GammaDeriv.lean (namespace Real, ~line 92-96);
that file proves Gamma' via harmonic numbers, NOT integrals — confirmed no
integral representation anywhere in Mathlib for this. Exponent derivative is
HasDerivAt.const_rpow (Pow/Deriv.lean:731), NOT hasDerivAt_const_rpow.
REMAINING: Obl 1 (dominating fn integrable — hardest of the small ones,
u^(-1/2)|log u| near 0), Obl 2 (pointwise domination), Obl 4 (THE WALL:
differentiation under the integral via
hasDerivAt_integral_of_dominated_loc_of_deriv_le), Target, and gap_five.

CFAC REFACTOR (2026-07-26): our G2C is the product over p>=3 of the REGULARISED
factors only — it is NOT the manuscript's G2 (which carries an extra
(1-2^-s)^z and (zeta(s)(s-1))^z). Rather than change G2C, Fbig was redefined:
  Fbig s z = (cFac s)^z * (1 - z/2^s)^(-1) * G2C s z
  cFac s   = prod_{p>=3} (1 - p^-s)^(-1)   [ = zeta(s)(1-2^-s) ]
CONSEQUENCE: Fk_expansion's third factor is now (log (cFac s))^l / l!, NOT the
manuscript's (-log(s-1))^l / l!.  Lemma 2.4 / Prop 2.5 must be stated against
OUR normalisation, or a bridge lemma proved. Flag this when resuming.
All Theorem 4.1 machinery verified intact after the refactor (sentinels:
dyadic_term_bound, sum_ratio_log_dyadic', deltaM_upper_bound_manuscript).

=== LEMMA 2.2 COMPLETE (2026-07-27) ===
Fk_expansion is proven unconditionally on its hypotheses.
  L2b (triple Cauchy product) - was already done
  L2a - PROVEN today via:
    A1 zOmega_summable / zOmega_summable_radius
       (smooth-number machinery + Euler-factor bound; needed TWO Mathlib
        gaps filled: finset_prod_le_prod_nonneg, since Mathlib's ordered
        product API requires IsOrderedMonoid which R lacks under mult.)
    A2 zOmega_eulerProduct  (one line from EulerProduct)
    A3 eulerProduct_eq_Fbig (B1-B4: log_tprod_real [Mathlib gap],
       cFac_cpow, tail_regroup, split_two)
    A4 Fk_eq_coeff_tsum (C1 omega_pow_summable_radius, C2
       iteratedDeriv_tsum_eq, C3 iteratedDeriv_monomial_zero)

HYPOTHESES NOW THREADED through L2a / Fk_expansion (discharge later):
  hk : 1 <= k        -- A4 is FALSE at k=0 (n=1 has Omega=0 but Fk excludes it)
  hc : 0 < cFac s
  hmulR / hposR / hlogR : convergence facts for the p>=3 factor family
These are all true for s in (1,2]; proving them is a separate task.

MATHLIB GAPS FILLED (reusable, in Basic.lean):
  finset_prod_le_prod_nonneg   - product monotonicity for nonneg reals
  log_tprod_real               - log of an infinite product (any index type)
  hasProd_cexp_of_hasSum       - exp of a HasSum is a HasProd
  pow_le_const_mul_geom        - uniform polynomial-vs-geometric bound

WHAT REMAINS: the file has ONE sorry, erdos_sums_increase_from_six, and
NOTHING connects Lemma 2.2 to it yet.  Still to formalise:
  Lemma 2.4, Prop 2.5, Theorem 6.1 (Taylor-remainder variant of L2b),
  Theorem 7.1 (far range), the range decomposition, and real definitions
  for S*, alpha_+, Gamma.  Also: discharge the hc/hmulR/hposR/hlogR
  hypotheses, and note the cFac normalisation means Fk_expansion's third
  factor is (log (cFac s))^l / l!, NOT the manuscript's (-log(s-1))^l / l!.

=== LEMMA 3.9 COMPLETE (real and complex) ===
lemma_3_9_complex : d/ds G2manu = G2manu * (z*(f s + log2/(2^s-1)) + sum_{p>=3} ...)
  -- the manuscript's G2^(1,0) = z G2 c, in MULTIPLIED form (not logarithmic).
lemma_3_9_real    : the same for real z, via log_reg_tprod_real.
f = (log zetaTilde)' is a HYPOTHESIS in both (manuscript certifies it from
FLINT Stieltjes constants; Mathlib's zeta is complex so its reality on the
real axis would be a separate obligation).

THE KEY DESIGN DECISION: never take Complex.log of the product.
Branch cuts make log(prod) = sum(log) false in general, so the real proof's
route (log_tprod_real) has NO complex analogue.  Instead every step goes
through exp of a sum:
  G2tailC_eq_exp_sum / prime_factor_eq_exp_complex  express factors as exp
  HasDerivAt.cexp                                    differentiates them
This is why hasDerivAt_G2tailC and hasDerivAt_prime_three_factor look the way
they do.  Do not try to "simplify" them back to a log formulation.

CHAIN (all proven, in dependency order):
  one_sub_mem_slitPlane            side condition for Complex.hasDerivAt_log
  hasDerivAt_rpow_neg              d/dt p^(-t), shared real/complex
  deriv_clog_one_sub_const_rpow    via HasDerivAt.scomp (R-param, C-valued)
  deriv_clog_prime_factor          per-prime, Complex.log second term
  deriv_clog_prime_factor_canon    per-prime, REAL log second term (p >= 3)
  deriv_clog_term_bound_uniform    ||.|| <= 27 log p p^(-2)
  deriv_bound_uniform_summable_five, clog_series_summable_at_basepoint
  hasDerivAt_clog_series           termwise, via hasDerivAt_tsum_of_isPreconnected
  hasDerivAt_G2tailC               cexp step: d/ds tail = tail * sum
  hasDerivAt_prime_three_factor    same for the p=3 factor
  hasDerivAt_G2C                   product rule
  hasDerivAt_kappa_cpow            d/ds kappa^z
  lemma_3_9_complex                product rule again

LEAN LESSONS FROM THIS SESSION (each cost multiple rounds):
  * convert h using 1 on a HasDerivAt goal splits into INSTANCE goals
    (Semiring.toModule = ...).  ALWAYS use instead:
       have hval : <target> = <what h has> := by field_simp / ring
       rw [hval]; exact h
  * push_cast rewrites |(Real.log x) into Complex.log |x -- equal but NOT
    syntactically interchangeable.  Do not push_cast in the complex chain.
    Complex.ofReal_inv and Complex.ofReal_log are the safe targeted moves.
  * hasDerivAt_tsum_of_isPreconnected TIMES OUT unless g and g' are supplied
    explicitly with (g := ...) (g' := ...).
  * to_additive-generated names (HasSum.add_compl, hasSum_subtype_iff_indicator)
    do NOT appear in Mathlib source -- grep finds nothing.  Find the
    multiplicative name, then mechanically drop mul_->add_, prod->sum.
  * A two-line "#check @name" probe appended to the file settles a name in ONE
    round.  Far cheaper than grepping.
  * When nlinarith fails on products: name each intermediate with
    mul_le_mul_of_nonneg_left, then close with linarith.

=== NEXT: LEMMA 3.8 (contour differentiation) ===
Have: gManu_eq_cauchy_coeff (g_i as a Cauchy coefficient at R = 12/5),
      G2manu_differentiableOn_wide, and now lemma_3_9_complex as the
      pointwise s-derivative.
Need: differentiate the contour integral in s.
  cauchyPowerSeries f c R n = (2 pi I)^-1 . contour (z-c)^-1^n (z-c)^-1 f z
  (Mathlib/MeasureTheory/Integral/CircleIntegral.lean:592)
  so unfold circleIntegral to an integral over [0, 2pi] and apply
  hasDerivAt_integral_of_dominated_loc_of_deriv_le (the EulerGamma pattern).
DECISION: M1 = 2544 >= sup_{s in [1,2], |z|=2.9} |G2^(1,0)| enters as a
  HYPOTHESIS, matching section 3.5 (certified by interval-arc evaluation in
  Arb, not by hand).  With M1 assumed, 3.8 is differentiation-under-the-
  integral MECHANICS, not a new estimate.
Only r <= 2 is ever used (section 3.5 needs r=1, Theorem 6.1 needs r=2);
C^infinity is never consumed.

=== COMPLETE ===
erdos_sums_increase_from_six : forall k, 6 <= k -> f k < f (k+1)
Zero sorries.  Axioms: propext, Classical.choice, Quot.sound only.

MACHINE-VERIFIED (the analytic reduction, end to end):
  Section 2  Lemmas 2.1, 2.2, Def 2.3, 2.4, Proposition 2.5 (exact identity)
             plus sum c_i = 1/2 and sum 2^i c_i = d
  Section 3  Lemma 3.9 (real and complex), Lemma 3.8 (r=1 and r=2),
             section 3.5's mean-value step, manuscript (4), manuscript (10),
             |E_1(k)| <= alpha_+(k+1)
  Section 4  Theorem 4.1, both bounds
  Section 6  Theorem 6.1, including the k-INDEPENDENCE of Gamma
             (geom_two_three: sum_l 2^l 3^(-l-1) = 1)
  Section 7  Theorem 7.1, by induction from phi(k1) > 0
  Assembly   the four ranges, no gaps

ASSUMED (NumericalFacts, plus the analytic-layer certified inputs):
  d, rho enclosures; S*, alpha_+, Gamma bounds; Umax, Vmax
  phi(2440) > 0 and phi monotone above 2440; the aggregate source bound
  the three criterion sweeps: [6,199], [79,899], [900,2439]
  f = (log zetaTilde)' and f'; contour sups M, M0, M2; beta_i and gammahat_i

THE CAVEAT THAT MATTERS: NumericalFacts is a hypothesis.  The theorem is
vacuous unless an instance exists, and the instance comes from the Arb
computations OUTSIDE Lean.  This is exactly Caveat 1.3(b)'s division, drawn
explicitly rather than blurred -- but it means the correct claim is "the
analytic reduction is machine-verified", NOT "Lean proved the theorem".

DOCUMENTED DEVIATIONS FROM THE MANUSCRIPT:
  contour radius 2, not 2.9 (the proven analyticity radius is 5/2, and
    lemma_3_9_complex holds for ||z|| <= 2) -- so M, M0, M2 are sups at 2
  M2k indexed from i = 0, not i = 1; equal since bHat_0 = 0, which is TRUE
    (every cBracket term carries a factor of z) but NOT PROVED here

VACUITIES FOUND AND CLOSED (each invisible on paper):
  cFac's multipliability -- Lemma 2.2's convergence hypotheses
  dConst's convergence -- d_enclosure was about a tprod junk value
  Sm's integrability -- LOAD-BEARING under Am, deltaM and Theorem 4.1


=== ODD CASE (2026-08-22) ===

fOdd_decreasing : forall k, 1 <= k -> fOdd (k+1) < fOdd k
Zero sorries.  Axioms: propext, Classical.choice, Quot.sound only.
Audit: lake env lean odd-proof/axcheck.lean -- 14 theorems, all clean.

WHAT THE FORMALIZATION FOUND.  PROOF.md section 5.1 carried an unquantified
"(lower order)" in the remainder bound.  Making it explicit turned up three
things it was hiding, and two of them are not lower order:

  * the two coefficient tails.  The main terms integrate to PARTIAL sums over
    j <= k, so sum_{j>k} h_j(1) and 2^-(k+1) sum_{j>k}(b_j + 2 gamma h_j(1))2^j
    join R_k.  Bounded by the same pole-cancellation device at first and second
    order: S_0 <= 44.6, S_1 <= 453.1.  These ARE small (5e-8 and 5e-5 of the
    budget at k = 59).

  * the Jacobian and product errors.  The split leaves three error terms, not
    one: besides the Lagrange remainder R_j J, also h_j(1)(J - e^-u - 2 gamma
    e^-2u) and b_j(eps J - e^-2u).  The combined constant is CE <= 5.48910 where
    the old bound implicitly used 3.  This is the dominant correction: it takes
    C from 2402.3 to 4838, and K0 from 57 to 59.

  * the near region u <= U.  The expansions hold only for u >= U = 3; below
    that the integrand is bounded directly (CN <= 367.8435, NEARU <= 24.6769).

The certified sweep reaches k = 60, so the ranges still overlap at 59,60 and
the theorem stands -- but with a two-value margin rather than four.

LEAN LESSONS FROM THIS SESSION:

  * READ THE SIGNATURE.  Summable.congr, Set.subset_union_left, div_le_iff0,
    abs_add_le, one_le_pow0, IntegrableOn.congr_fun -- each cost 3-6 rounds of
    permuting call shapes when one grep at the Mathlib source would have
    settled it.  Rule: if an application fails twice, stop and read the type.

  * ORPHANED DOCSTRINGS.  Inserting a theorem between a /-- ... -/ and its
    declaration produces "unexpected token '/--'; expected 'lemma'" at a line
    number that points at the SECOND docstring, not the orphan.  Cost several
    rounds each time.  Always splice above the docstring, never between.

  * DUPLICATE HYPOTHESIS NAMES SHADOW SILENTLY.  A stale `have hre2 : HasSum
    ... := by sorry` left above the real `have hre2 : ... = ...` meant rw
    [<- hre2] used the sorry'd one.  Eight rounds of misdiagnosis, blamed on
    set/let unfolding.  Check for duplicates before blaming elaboration.

  * INTERVAL ARITHMETIC AND THE DEPENDENCY PROBLEM.  The four constants behind
    CE are ratios in which zeta's pole at s=1 cancels.  Evaluating them on
    boxes of s loses the cancellation -- arb sees each occurrence of (s-1)
    independently -- and the enclosures diverge NO MATTER how narrow the boxes.
    Five approaches failed this way (direct sums, MVT, Euler-Maclaurin, expm1
    regularization, the eta function).  The fix is a Taylor model: expand zeta
    as an arb_series about 1 + E/2, form the constants as series so the
    cancellation is SYMBOLIC, then evaluate on the whole disc at once.  One
    shot, tight, no monotonicity assumed.  arb_series.zeta exists and is the
    right tool; reach for it whenever a bound involves cancelling singularities.

  * DEAD PROOF CODE INTERLEAVES.  The superseded tail route could not be
    excised at the end: its `have`s sit between live ones.  Remove abandoned
    branches when you abandon them, not later.
