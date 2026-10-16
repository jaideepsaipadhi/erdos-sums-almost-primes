import Banksmartin.Basic

/-!
# The odd Erdos sums

    f_k^odd = sum over odd n >= 3 with Omega(n) = k of 1/(n log n)

CONJECTURE (Lichtman): f_k^odd is strictly decreasing for every k >= 1.

Reuses Banksmartin.Basic wherever the objects are already p >= 3.  The
manuscript's normalisation pulls the p = 2 factor out separately, so cFac,
G2C, dConst and rhoConst there ARE the odd Euler product objects, and DBound,
deltaConv_le, deltaM_abs_le, A2m_le, crit_pos_iff and theorem_7_1 are stated
generically enough to apply unchanged.

THE PROOF (odd-proof/PROOF.md, derived and verified 2026-08-01):

  f_k^odd = 1/2 + beta 2^-k + R_k,   beta = d (log 2 - S + gamma) = 0.15563

with S = sum_{p>=3} log p/((p-1)(p-2)), and |R_k| <= M_R R^-k by Cauchy on
|z| = R < 5 applied to Htilde(s,z) = H(s,z)(1 - z 3^-s).  With M_R <= 826.71
at R = 4.5 the inequality holds for k >= 12; k = 1..11 is certified directly.

THE STRUCTURAL POINT.  H(s,z) = (1-2^-s)^z prod_{p>=3}(1-z p^-s)^-1(1-p^-s)^z
is analytic in |z| < 3^s, so z = 2 lies strictly INSIDE.  In the unrestricted
problem the corresponding function is analytic only in |z| < 2^s and z = 2 is
ON the boundary -- that is what produces the k^2 competing with 2^-k, hence
the turnaround at k = 6 and all of sections 4-7 of the main development.

Numerics in odd-proof/README.md: f_k^odd certified for k = 1..20, strictly
decreasing, tending to 1/2 from above.
-/

open Real BigOperators
noncomputable section

/-- The Erdos sum restricted to odd n. -/
def fOdd (k : ℕ) : ℝ :=
  ∑' n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}, 1 / ((n : ℝ) * Real.log n)

-- The limit f_k^odd -> 1/2 is derived in odd-proof/PROOF.md section 3 (it is
-- H(1,1) = 1 - 2^-1, the omitted Euler factor at z = s = 1) and confirmed
-- numerically to k = 20.  It is not formalized here because the decreasing
-- theorem does not use it.



/-- F_k(s) := Σ_{Ω(n)=k} n^{-s}, the Dirichlet series restricted to
    k-almost-primes. -/
noncomputable def FkOdd (k : ℕ) (s : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}, (n : ℝ) ^ (-s)

/-- F_k(s) is summable for s > 1. -/
lemma FkOdd_summable (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} => (n : ℝ) ^ (-s)) := by
  have hcomp : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact hcomp.subtype _

/-- The Tonelli exchange: f_k = ∫₁^∞ F_k(s) ds. -/
lemma fOdd_eq_integral_FkOdd (k : ℕ) (hk : 1 ≤ k)
    (hsum1 : Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n))) :
    fOdd k = ∫ s in Set.Ioi (1 : ℝ), FkOdd k s := by
  unfold fOdd FkOdd
  have habs : ∀ (n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}) (s : ℝ),
      ‖(n : ℝ) ^ (-s)‖ = (n : ℝ) ^ (-s) := by
    intro n s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm_eq : ∀ n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k},
      ∫ s in Set.Ioi (1 : ℝ), ‖(n : ℝ) ^ (-s)‖ = 1 / ((n : ℝ) * Real.log n) := by
    intro n
    simp_rw [habs]
    exact integral_n_neg_s n (by omega : 2 ≤ (n : ℕ))
  have hsummable_norm : Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      ∫ s in Set.Ioi (1 : ℝ), ‖(n : ℝ) ^ (-s)‖) := by
    simp_rw [hnorm_eq]; exact hsum1
  have hint : ∀ n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k},
      MeasureTheory.Integrable (fun s => (n : ℝ) ^ (-s))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    intro n
    by_contra hni
    have hz := MeasureTheory.integral_undef hni
    rw [integral_n_neg_s n (by omega : 2 ≤ (n : ℕ))] at hz
    have : (0 : ℝ) < 1 / ((n : ℝ) * Real.log n) := by
      have hn2 : 2 ≤ (n : ℕ) := (by omega : 2 ≤ (n : ℕ))
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < (n : ℕ))
      have := Real.log_pos this
      positivity
    linarith [hz ▸ this]
  rw [tsum_congr (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} => (integral_n_neg_s n (by omega : 2 ≤ (n : ℕ))).symm)]
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable_norm


/-- S = sum over odd primes of log p / ((p-1)(p-2)).

Certified enclosure [0.8593920314, 0.8593986014]: head to 5e6 plus the tail
bound sum_{n>P} 2 log n / n^2 < 2(log P + 1)/P. -/
noncomputable def Sodd : ℝ := ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
  Real.log p / (((p : ℝ) - 1) * ((p : ℝ) - 2))

/-- The leading coefficient of the odd expansion,
beta = d (log 2 - S + gamma), numerically 0.15563. -/
noncomputable def betaOdd : ℝ :=
  dConst * (Real.log 2 - Sodd + Real.eulerMascheroniConstant)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 0 in
/-- `0.57715 < gamma`.  This was `OddNumericalFacts.gamma_gt`, an assumed
field, until it was proved here.

Mathlib's only lower bound is `one_half_lt_eulerMascheroniConstant`, too weak
here.  The usable route is `eulerMascheroniSeq_lt_eulerMascheroniConstant`,
`harmonic n - log (n+1) < gamma`, whose gap to `gamma` is about `1/(2n)`.

`n = 8191` is chosen so that `n + 1 = 8192 = 2^13` and the logarithm is
`13 log 2` EXACTLY.  That matters: the margin here is `4.55e-6`, and Mathlib's
`log 2` is good to `3.4e-9`, whereas any `n + 1` that is not a power of two
would need a bound on `log (n+1)` of its own -- at `n = 7614`, the smallest n
that works at all, to `4e-7`, where the obvious bound is off by `2.6e-3`.

    harmonic 8191        = 9.588067975783...
    lower bound used     = 9.5880679        (margin 4.55e-6)
    0.57715 + 13 log 2  <= 9.588063350400

Using 9.5880634 instead, as this did at first, leaves a margin of 4.96e-8 --
true, but a hundred times thinner for nothing.
-/
theorem gamma_lower_bound : (0.57715 : ℝ) < Real.eulerMascheroniConstant := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 8191
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog : Real.log 8192 = 13 * Real.log 2 := by
    rw [show (8192:ℝ) = 2 ^ (13:ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  -- Explicit fractions, not decimals: `9.5880634` elaborates through
  -- `OfScientific`, which `exact_mod_cast` will not carry across ℚ → ℝ
  -- ("mod_cast has type" at this line before the change).
  have hH : (95880679 / 10000000 : ℚ) < harmonic 8191 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hHr : (95880679 / 10000000 : ℝ) < (harmonic 8191 : ℝ) := by
    exact_mod_cast hH
  have hlow : (0.57715 : ℝ) < (harmonic 8191 : ℝ) - Real.log 8192 := by
    rw [hlog]; linarith
  simp only [Real.eulerMascheroniSeq] at hseq
  try norm_num at hseq
  linarith [hseq, hlow]

/-- The certified inputs the odd theorem assumes.

As in the main development these are Arb ball computations, not formalized
results.  `Sodd_enclosure` and `MR_bound` come from odd-proof/numerics/, `d` is
already certified in Banksmartin.Basic, and `sweep_low` is the certified
sweep over the range below the analytic threshold. -/
structure OddNumericalFacts (MR : ℝ) : Prop where
  /-- The certified enclosure of S. -/
  Sodd_enclosure : |Sodd - 0.8593953| ≤ 3.3e-6
  /-- Cauchy bound: the sup of |Htilde| on |z| = 4.5, s in [1,2]. -/
  MR_bound       : MR ≤ 4900
  /-- The remainder bound that Cauchy's estimate yields. -/
  remainder      : ∀ k : ℕ, |fOdd k - 1 / 2 - betaOdd * ((1:ℝ)/2) ^ k|
                     ≤ MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
  /-- Certified sweep below the analytic threshold. -/
  sweep_low      : ∀ k : ℕ, 1 ≤ k → k ≤ 58 → fOdd (k + 1) < fOdd k
/-- The arithmetic core of the odd assembly, with all rpow stripped out.

A = f_k, B = f_{k+1}, P = 2^-k, T = MR (k+3)^3 3^-k, b = beta; T <= 0.048 P for k >= 59.  The two
enclosures give A >= bP - T and B <= bP/2 + 2T/9, so
A - B >= bP/2 - T(1.3503) >= P(0.1556/2 - 0.048*1.3503) = 0.0130 P > 0. -/
theorem odd_step (b P T A B : ℝ)
    (hb : (0.1556 : ℝ) ≤ b) (hP : 0 < P) (hT : 0 ≤ T)
    (hTb : T ≤ (0.048 : ℝ) * P)
    (hA : |A - b * P| ≤ T)
    (hB : |B - b * P / 2| ≤ T * (3503/10000)) :
    B < A := by
  have hA1 := (abs_le.mp hA).1
  have hB2 := (abs_le.mp hB).2
  nlinarith [hA1, hB2, hTb, hP, hT, hb]

/-- (k+3)^3 (2/3)^k is antitone for k >= 4: the ratio is
((k+4)/(k+3))^3 (2/3) < 1 as soon as (1 + 1/(k+3))^3 < 3/2, i.e. k+3 > 6.5.
This replaces the geometric factorisation the old purely-exponential bound
used; with T = MR (k+3)^3 3^-k there is no such factorisation. -/
theorem polyGeom_step (k : ℕ) (hk : 4 ≤ k) :
    ((k:ℝ) + 4) ^ 3 * ((2:ℝ)/3) ^ (k+1) ≤ ((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k := by
  have hk4 : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hpos : (0:ℝ) < ((2:ℝ)/3) ^ k := pow_pos (by norm_num) k
  have h3 : (0:ℝ) < (k:ℝ) + 3 := by linarith
  have hcube : ((k:ℝ) + 4) ^ 3 * (2/3) ≤ ((k:ℝ) + 3) ^ 3 := by
    -- 3(k+3)^3 - 2(k+4)^3 = (k-4)(k^2+7k+13) + 5 >= 5 > 0 for k >= 4
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) - 4)
                 (by nlinarith : (0:ℝ) ≤ (k:ℝ)^2 + 7*(k:ℝ) + 13)]
  have he : ((2:ℝ)/3) ^ (k+1) = ((2:ℝ)/3) ^ k * (2/3) := pow_succ _ _
  rw [he]
  calc ((k:ℝ)+4)^3 * (((2:ℝ)/3)^k * (2/3))
      = (((k:ℝ)+4)^3 * (2/3)) * ((2:ℝ)/3)^k := by ring
    _ ≤ ((k:ℝ)+3)^3 * ((2:ℝ)/3)^k :=
        mul_le_mul_of_nonneg_right hcube (le_of_lt hpos)

theorem polyGeom_antitone (k : ℕ) (hk : 59 ≤ k) :
    ((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k ≤ (62:ℝ) ^ 3 * ((2:ℝ)/3) ^ 59 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep := polyGeom_step n (by omega)
      push_cast at hstep ⊢
      linarith [hstep, ih]

/-- The odd theorem, conditional on the certified inputs.

For k >= 12 the leading term beta 2^-k dominates the Cauchy-bounded remainder;
below that the certified sweep covers it.  See odd-proof/PROOF.md section 6. -/
theorem fOdd_decreasing_of_facts (MR : ℝ) (hMR0 : 0 ≤ MR)
    (hnum : OddNumericalFacts MR) :
    ∀ k : ℕ, 1 ≤ k → fOdd (k + 1) < fOdd k := by
  intro k hk
  by_cases hsmall : k ≤ 58
  · exact hnum.sweep_low k hk hsmall
  · have hk57 : 59 ≤ k := by omega
    set P : ℝ := ((1:ℝ)/2) ^ k with hPdef
    have hP : 0 < P := pow_pos (by norm_num) k
    set T : ℝ := MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k with hTdef
    have hT : 0 ≤ T := by
      rw [hTdef]
      apply mul_nonneg (mul_nonneg hMR0 (by positivity))
      exact pow_nonneg (by norm_num) k
    -- T/P = MR (k+3)^3 (2/3)^k, antitone in k, so bounded by its value at 57
    have hTb : T ≤ (0.048:ℝ) * P := by
      rw [hTdef, hPdef]
      have hsplit : ((1:ℝ)/3) ^ k = ((2:ℝ)/3) ^ k * ((1:ℝ)/2) ^ k := by
        rw [← mul_pow]; norm_num
      rw [hsplit]
      have hmono := polyGeom_antitone k hk57
      have hhalf : (0:ℝ) < ((1:ℝ)/2) ^ k := pow_pos (by norm_num) k
      have hgpos : (0:ℝ) ≤ ((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k := by positivity
      have hnum60 : (4900:ℝ) * ((62:ℝ) ^ 3 * ((2:ℝ)/3) ^ 59) ≤ (0.048:ℝ) := by
        norm_num
      have hMRb := hnum.MR_bound
      have stepA : MR * (((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k)
          ≤ (4900:ℝ) * ((62:ℝ) ^ 3 * ((2:ℝ)/3) ^ 59) := by
        calc MR * (((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k)
            ≤ (4900:ℝ) * (((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k) :=
              mul_le_mul_of_nonneg_right hMRb hgpos
          _ ≤ (4900:ℝ) * ((62:ℝ) ^ 3 * ((2:ℝ)/3) ^ 59) :=
              mul_le_mul_of_nonneg_left hmono (by norm_num)
      calc MR * (((k:ℝ) + 3) ^ 3) * (((2:ℝ)/3) ^ k * ((1:ℝ)/2) ^ k)
          = (MR * (((k:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ k)) * ((1:ℝ)/2) ^ k := by ring
        _ ≤ ((4900:ℝ) * ((62:ℝ) ^ 3 * ((2:ℝ)/3) ^ 59)) * ((1:ℝ)/2) ^ k :=
              mul_le_mul_of_nonneg_right stepA (le_of_lt hhalf)
        _ ≤ (0.048:ℝ) * ((1:ℝ)/2) ^ k :=
              mul_le_mul_of_nonneg_right hnum60 (le_of_lt hhalf)
    have hb : (0.1556 : ℝ) ≤ betaOdd := by
      unfold betaOdd
      have hg := gamma_lower_bound
      have hd := dConst_lower_bound_sharp
      have hS := abs_le.mp hnum.Sodd_enclosure
      have hl2 := Real.log_two_gt_d9
      -- the second factor, at the worst end of Sodd's enclosure and the
      -- proved lower bound for gamma
      have hfac : (0.4108985803 : ℝ)
          ≤ Real.log 2 - Sodd + Real.eulerMascheroniConstant := by
        linarith [hS.2]
      have hd0 : (0 : ℝ) ≤ dConst := by linarith
      calc (0.1556 : ℝ) ≤ 0.3786823 * 0.4108985803 := by norm_num
        _ ≤ dConst * (Real.log 2 - Sodd + Real.eulerMascheroniConstant) :=
            mul_le_mul hd hfac (by norm_num) hd0
    have hA : |(fOdd k - 1/2) - betaOdd * P| ≤ T := by
      rw [hPdef, hTdef]
      have := hnum.remainder k
      calc |(fOdd k - 1/2) - betaOdd * ((1:ℝ)/2) ^ k|
          = |fOdd k - 1/2 - betaOdd * ((1:ℝ)/2) ^ k| := by ring_nf
        _ ≤ MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := this
    have hB : |(fOdd (k+1) - 1/2) - betaOdd * P / 2| ≤ T * (3503/10000) := by
      have h := hnum.remainder (k+1)
      have e1 : ((1:ℝ)/2) ^ (k+1) = ((1:ℝ)/2) ^ k / 2 := by
        rw [pow_succ]; ring
      have e3 : ((1:ℝ)/3) ^ (k+1) = ((1:ℝ)/3) ^ k * (1/3) := pow_succ _ _
      have ecast : (((k+1:ℕ)):ℝ) + 3 = (k:ℝ) + 4 := by push_cast; ring
      rw [e1, e3, ecast] at h
      -- ((k+4)/(k+3))^3 / 3 <= 0.3503 for k >= 57, since (61/60)^3 = 1.05084
      have hratio : ((k:ℝ) + 4) ^ 3 * (1/3) ≤ ((k:ℝ) + 3) ^ 3 * (3503/10000) := by
        have hk57r : (59:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk57
        nlinarith [hk57r, sq_nonneg ((k:ℝ) + 3)]
      have h3pos : (0:ℝ) < ((1:ℝ)/3) ^ k := pow_pos (by norm_num) k
      rw [hPdef, hTdef]
      calc |(fOdd (k+1) - 1/2) - betaOdd * ((1:ℝ)/2) ^ k / 2|
          = |fOdd (k+1) - 1/2 - betaOdd * (((1:ℝ)/2) ^ k / 2)| := by ring_nf
        _ ≤ MR * (((k:ℝ) + 4) ^ 3) * (((1:ℝ)/3) ^ k * (1/3)) := h
        _ ≤ MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k * (3503/10000) := by
              have hr : MR * (((k:ℝ) + 4) ^ 3 * (1/3))
                  ≤ MR * (((k:ℝ) + 3) ^ 3 * (3503/10000)) :=
                mul_le_mul_of_nonneg_left hratio hMR0
              calc MR * (((k:ℝ) + 4) ^ 3) * (((1:ℝ)/3) ^ k * (1/3))
                  = (MR * (((k:ℝ) + 4) ^ 3 * (1/3))) * ((1:ℝ)/3) ^ k := by ring
                _ ≤ (MR * (((k:ℝ) + 3) ^ 3 * (3503/10000))) * ((1:ℝ)/3) ^ k :=
                      mul_le_mul_of_nonneg_right hr (le_of_lt h3pos)
                _ = MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k * (3503/10000) := by ring
    have := odd_step betaOdd P T (fOdd k - 1/2) (fOdd (k+1) - 1/2)
      hb hP hT hTb hA hB
    linarith [this]

/-- THE ODD THEOREM, conditional on the certified inputs -- exactly as
`erdos_sums_increase_from_six` is conditional on `NumericalFacts`.

`OddNumericalFacts` assumes the analytic content of odd-proof/PROOF.md sections 2-5:
the expansion f_k^odd = 1/2 + beta 2^-k + R_k and the Cauchy bound
|R_k| <= MR (39/100)^k.  What is proved here is section 6, the assembly. -/
theorem fOdd_decreasing (MR : ℝ) (hMR0 : 0 ≤ MR) (hnum : OddNumericalFacts MR) :
    ∀ k : ℕ, 1 ≤ k → fOdd (k + 1) < fOdd k :=
  fOdd_decreasing_of_facts MR hMR0 hnum

end

/-- H(s,z), the regularised odd Euler product:

    H(s,z) = (1 - 2^-s)^z * prod_{p>=3} (1 - z p^-s)^-1 (1 - p^-s)^z

so that prod_{p>=3}(1 - z p^-s)^-1 = zeta(s)^z H(s,z).  Analytic in |z| < 3^s;
this is the function whose values at z = 1 and z = 2 give the limit 1/2 and
the leading coefficient.  See odd-proof/PROOF.md section 2. -/
noncomputable def Hodd (s : ℝ) (z : ℂ) : ℂ :=
  (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z *
    ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p : ℝ) ^ (-s) : ℝ)) : ℂ) ^ z

/-- At z = 1 every factor of the product collapses:
(1 - p^-s)^-1 (1 - p^-s)^1 = 1.  So H(s,1) = 1 - 2^-s. -/
theorem Hodd_at_one (s : ℝ) (hs : 1 ≤ s) :
    Hodd s 1 = ((1 - (2:ℝ) ^ (-s) : ℝ) : ℂ) := by
  unfold Hodd
  have hterm : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - (1:ℂ) * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ)) : ℂ) ^ (1:ℂ) = 1 := by
    intro p
    have hp3 : (3:ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.2
    have hlt : ((p : ℝ) ^ (-s)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
      linarith
    have hne : (1 - (((p : ℝ) ^ (-s) : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [Complex.cpow_one, one_mul]
    push_cast
    field_simp
  rw [tprod_congr hterm]
  simp [Complex.cpow_one]

/-- The limit constant: H(1,1) = 1 - 1/2 = 1/2.  This is where the odd sums'
limit comes from -- the omitted Euler factor at z = s = 1.  See odd-proof/PROOF.md
section 3. -/
theorem Hodd_one_one : Hodd 1 1 = (1/2 : ℂ) := by
  rw [Hodd_at_one 1 le_rfl]
  norm_num

/-- At s = 1 the Hodd factors take their elementary form:
p^(-1) = 1/p, so the p-th factor is (1 - 2/p)^-1 (1 - 1/p)^2. -/
theorem Hodd_factor_at_two (p : {p : ℕ // p.Prime ∧ 3 ≤ p}) :
    (1 - (2:ℂ) * (((p : ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-(1:ℝ)) : ℝ)) : ℂ) ^ (2:ℂ)
      = (((1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have hp3 : (3:ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.2
  have hpinv : ((p : ℕ) : ℝ) ^ (-(1:ℝ)) = 1 / ((p : ℕ) : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  rw [hpinv]
  have h2 : (((1 - 1 / ((p : ℕ) : ℝ) : ℝ)) : ℂ) ^ (2:ℂ)
      = (((1 - 1 / ((p : ℕ) : ℝ) : ℝ)) : ℂ) ^ (2:ℕ) := by
    rw [← Complex.cpow_natCast]
    norm_num
  rw [h2]
  push_cast
  field_simp

/-- H(1,2) = d, the constant from the main development.

(1 - 1/2)^2 = 1/4 supplies dConst's prefactor, and the p-th factor matches
term for term by Hodd_factor_at_two.  See odd-proof/PROOF.md section 4. -/
theorem Hodd_one_two : Hodd 1 2 = ((dConst : ℝ) : ℂ) := by
  unfold Hodd dConst
  rw [dConst_prod_eq_subtype]
  have hpre : ((1 - (2:ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ) ^ (2:ℂ) = (1/4 : ℂ) := by
    rw [Real.rpow_neg_one]
    norm_num
  rw [hpre]
  -- the p-th factors agree, then push the cast through the product
  rw [tprod_congr Hodd_factor_at_two]
  have hmt := dConst_family_multipliable.map_tprod Complex.ofRealHom
        Complex.continuous_ofReal
  simp only [Complex.ofRealHom_eq_coe] at hmt
  rw [Complex.ofReal_mul, ← hmt]
  norm_num

/-- A prime p >= 5 that is not 5 is at least 7 (6 is not prime). -/
theorem seven_le_of_prime_ne_five {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hne : p ≠ 5) :
    7 ≤ p := by
  rcases Nat.lt_or_ge p 7 with h | h
  · interval_cases p
    · exact absurd rfl hne
    · exact absurd hp (by decide)
  · exact h

/-- The complement of {b5} in the p >= 3 primes is equivalent to the p >= 5 primes. -/
def compl_b5_equiv :
    (({⟨ 5, (by norm_num : Nat.Prime 5), le_refl 5 ⟩} : Set {p : ℕ // p.Prime ∧ 5 ≤ p})ᶜ :
      Set {p : ℕ // p.Prime ∧ 5 ≤ p}) ≃ {p : ℕ // p.Prime ∧ 7 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2.1, by
    have hne : q.1.1 ≠ 5 := by
      intro h
      apply q.2
      apply Subtype.ext
      exact h
    exact seven_le_of_prime_ne_five q.1.2.1 q.1.2.2 hne ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1, by have := r.2.2; omega ⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h5 := r.2.2
    have : r.1 = 5 := congrArg Subtype.val h
    omega ⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl



/-- If the p >= 7 tail is multipliable, so is the p >= 5 family, and the
product splits off the p = 5 factor. -/
theorem tprod_split_five {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    [ContinuousMul M] (f : ℕ → M)
    (hf5 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => f p)) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)
      ∧ (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p)
        = f 5 * ∏' p : {p : ℕ // p.Prime ∧ 7 ≤ p}, f p := by
  classical
  set b5 : {p : ℕ // p.Prime ∧ 5 ≤ p} := ⟨ 5, (by norm_num : Nat.Prime 5), le_refl 5 ⟩ with hb5
  set g : {p : ℕ // p.Prime ∧ 5 ≤ p} → M := fun p => f p with hg
  have hsingle : HasProd ((({b5} : Set {p : ℕ // p.Prime ∧ 5 ≤ p}).restrict g)) (g b5) := by
    have := hasProd_singleton b5 g
    exact this
  have hcompl : HasProd (((({b5} : Set {p : ℕ // p.Prime ∧ 5 ≤ p})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 7 ≤ p}, f p) := by
    have hbase : HasProd (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => f p)
        (∏' p : {p : ℕ // p.Prime ∧ 7 ≤ p}, f p) := hf5.hasProd
    exact (compl_b5_equiv.hasProd_iff).mpr hbase
  have hequiv : Multipliable (((({b5} : Set {p : ℕ // p.Prime ∧ 5 ≤ p})ᶜ).restrict g)) :=
    hcompl.multipliable
  have hall := hsingle.mul_compl hcompl
  refine ⟨ hall.multipliable, ?_⟩
  rw [hall.tprod_eq]


/-- The p >= 7 Euler tail of Hodd, the analogue of G2tailC one prime along.
Analytic in |z| < 7^s, which is what lets Htilde be handled at radius 4. -/
noncomputable def HoddTail (s : ℝ) (z : ℂ) : ℂ :=
  ∏' p : {p : ℕ // p.Prime ∧ 7 ≤ p},
    (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z

/-- Radius-4 variant: 43 p^(-2s) <= 1 for p >= 7 (43 / 49 = 0.878). -/
theorem correction_le_one_seven (p : ℕ) (hp : 7 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    43 * (p : ℝ) ^ (-2*s) ≤ 1 := by
  have hp7 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : (p : ℝ) ^ (-2*s) ≤ (p : ℝ) ^ (-2:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpow : (7 : ℝ) ^ (2 : ℝ) ≤ (p : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hp7 (by norm_num)
  have heq7 : (7 : ℝ) ^ (-2:ℝ) = ((7 : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) 2
  have heqp : (p : ℝ) ^ (-2:ℝ) = ((p : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg hpos.le 2
  have h2 : (p : ℝ) ^ (-2:ℝ) ≤ (7 : ℝ) ^ (-2:ℝ) := by
    rw [heqp, heq7]
    gcongr
  have h5val : (7 : ℝ) ^ (-2:ℝ) = 1 / 49 := by
    rw [heq7]
    norm_num [Real.rpow_natCast]
  have hchain : (p : ℝ) ^ (-2*s) ≤ 1 / 49 := le_trans h1 (h2.trans_eq h5val)
  linarith [hchain]


/-- Wide-radius variant: ||z|| <= 4 for p >= 5, constant 24.
Needed to place z = 2 strictly inside the disc of analyticity, which is what
sum 2^i c_i = d requires. -/
theorem prime_correction_bound_complex_seven (p : ℕ) (hp : 7 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 4) :
    ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖
      ≤ 43 * (p : ℝ) ^ (-2*s) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 7 := by
    rw [ha_def]
    have hp3 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 7 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z : ℂ) * (a : ℂ)‖ ≤ 4 / 7 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ (4) * (1 / 7) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt1 : ‖(z : ℂ) * (a : ℂ)‖ < 1 := by linarith
  have hr1 := complex_log_bound ((z : ℂ) * (a : ℂ)) hza_lt1
  have hr2 := log_bound_combined_fifth a (by rw [abs_of_pos ha_pos]; linarith)
  have hr1bound : ‖z * (a : ℂ)‖^2 / (1 - ‖z * (a : ℂ)‖) ≤ (112 / 3) * a^2 := by
    have h1 : ‖z * (a : ℂ)‖ ≤ (4) * a := by
      rw [norm_mul, hane]; nlinarith [hz]
    have h2 : (3 : ℝ)/7 ≤ 1 - ‖z * (a : ℂ)‖ := by linarith [hza_le]
    have h3 : ‖z * (a : ℂ)‖^2 ≤ (16) * a^2 := by
      nlinarith [h1, norm_nonneg (z * (a : ℂ))]
    calc ‖z * (a : ℂ)‖^2 / (1 - ‖z * (a : ℂ)‖) ≤ ‖z * (a : ℂ)‖^2 / (3 / 7) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h2
      _ = (7 / 3) * ‖z * (a : ℂ)‖^2 := by ring
      _ ≤ (7 / 3) * ((16) * a^2) := by linarith [h3]
      _ ≤ (112 / 3) * a^2 := by nlinarith [sq_nonneg a]
  have hkey : (-Complex.log (1 - z * (a : ℂ))) + z * (Real.log (1 - a) : ℂ)
      = -(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
          z * ((Real.log (1 - a) : ℂ) + (a : ℂ)) := by ring
  rw [hkey]
  have hstep1 : ‖-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖
      ≤ ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ := by
    have := norm_add_le (-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)))
      (z * ((Real.log (1 - a) : ℂ) + (a : ℂ)))
    rwa [norm_neg] at this
  have hstep2 : ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ ≤ ‖z‖ * ((5 / 4) * a^2) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have heq : ((Real.log (1 - a) : ℂ) + (a : ℂ)) = ((Real.log (1 - a) + a : ℝ):ℂ) := by
      push_cast; ring
    rw [heq]
    first
    | rw [Complex.norm_real]; exact hr2
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact hr2
  have hfinal_bound : ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
      ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ ≤ (112 / 3) * a^2 + ‖z‖ * ((5 / 4) * a^2) := by
    linarith [hr1, hr1bound, hstep2]
  calc ‖-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖
      ≤ ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ := hstep1
    _ ≤ (112 / 3) * a^2 + ‖z‖ * ((5 / 4) * a^2) := hfinal_bound
    _ ≤ (112 / 3) * a^2 + (4) * ((5 / 4) * a^2) := by nlinarith [hz, sq_nonneg a]
    _ ≤ 43 * a^2 := by nlinarith [sq_nonneg a]
    _ = 43 * (p : ℝ) ^ (-2*s) := by
        rw [ha_def, ← Real.rpow_natCast ((p : ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
        ring_nf


/-- Wide-radius variant: ||z|| <= 4, constant 48. -/
theorem prime_factor_sub_one_bound_complex_seven (p : ℕ) (hp : 7 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 4) :
    ‖Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖
      ≤ 86 * (p : ℝ) ^ (-2*s) := by
  set c : ℂ := (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
    z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) with hc_def
  have hp3 : 7 ≤ p := by omega
  have hbound : ‖c‖ ≤ 43 * (p : ℝ) ^ (-2*s) := prime_correction_bound_complex_seven p hp3 s hs z hz
  have hle1 : 43 * (p : ℝ) ^ (-2*s) ≤ 1 := correction_le_one_seven p hp s hs
  have hc1 : ‖c‖ ≤ 1 := le_trans hbound hle1
  calc ‖Complex.exp c - 1‖ ≤ 2 * ‖c‖ := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (43 * (p : ℝ) ^ (-2*s)) := by linarith [hbound]
    _ = 86 * (p : ℝ) ^ (-2*s) := by ring


/-- Wide-radius variant (||z|| <= 4). -/
theorem prime_factor_sub_one_summable_complex_seven (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 4) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      ‖Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => 86 * (p : ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 7 ≤ p}, (86 : ℝ) * (p : ℝ) ^ (-2*s) =
        86 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 86
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      prime_factor_sub_one_bound_complex_seven (p : ℕ) p.property.2 s hs z hz)
    hcomp


/-- Wide-radius variant. -/
theorem prime_factor_eq_exp_complex_seven (p : ℕ) (hp : 7 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 4) :
    (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
      Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 7 := by
    rw [ha_def]
    have hp3 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 7 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z : ℂ) * (a : ℂ)‖ ≤ 29 / 50 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ (4) * (1 / 7) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt : ‖(z : ℂ) * (a : ℂ)‖ < 1 := by linarith
  have h1za_ne : (1 : ℂ) - z * (a : ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1 : ℝ) = ‖z * (a : ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)):ℂ) ^ z =
      Complex.exp (Complex.log (((1 - a : ℝ)):ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne]
  have key : Complex.exp ((-Complex.log (1 - z * (a : ℂ))) +
      z * ((Real.log (1 - a) : ℝ):ℂ)) =
      (1 - z * (a : ℂ))⁻¹ * (((1 - a : ℝ)):ℂ) ^ z := by
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_log h1za_ne, hcpow, ← hlog1a,
      show z * Complex.log (((1 - a : ℝ)):ℂ) = Complex.log (((1 - a : ℝ)):ℂ) * z
        from mul_comm _ _]
  exact key.symm



/-- Wide-radius variant (||z|| <= 4). -/
theorem prime_factor_multipliable_complex_seven (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 4) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable_complex_seven s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      1 + (Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 7 ≤ p},
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
          (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
        1 + (Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1) := by
    intro p
    have hp3 : 7 ≤ (p : ℕ) := p.property.2
    rw [prime_factor_eq_exp_complex_seven (p : ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult


/-- Wide-radius variant: the tail product converges for ||z|| <= 4. -/
theorem HoddTail_hasProd_seven (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 4) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * ((((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ)) : ℂ)) ^ z)
      (HoddTail s z) :=
  (prime_factor_multipliable_complex_seven s hs z hz).hasProd


/-- Wide-radius variant (radius 4, p >= 5). -/
theorem correction_differentiableOn_seven (p : ℕ) (hp : 7 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
      z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) (Metric.ball 0 (4)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 7 := by
    rw [ha_def]
    have hp3 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 7 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_lt : ‖z * (a : ℂ)‖ < 1 := by
    rw [norm_mul, hane]; nlinarith [hz, ha_le, ha_pos]
  have hre_pos : (0 : ℝ) < ((1 : ℂ) - z * (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    have hre_le_norm : |z.re| ≤ ‖z‖ := by
      have hns : z.re^2 ≤ Complex.normSq z := by
        have : Complex.normSq z = z.re^2 + z.im^2 := by
          rw [Complex.normSq_apply]; ring
        nlinarith [sq_nonneg z.im, this]
      have hnormsq : ‖z‖^2 = Complex.normSq z := by
        first
        | rw [Complex.norm_eq_abs, Complex.abs_apply, Real.sq_sqrt (Complex.normSq_nonneg z)]
        | rw [Complex.sq_norm]
        | rw [Complex.norm_sq_apply]
        | exact (Complex.normSq_eq_abs z).symm ▸ (Complex.sq_abs z)
        | rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]
      have hsq : z.re^2 ≤ ‖z‖^2 := by rw [hnormsq]; exact hns
      nlinarith [abs_nonneg z.re, norm_nonneg z, sq_abs z.re, hsq]
    have hre_le : z.re * a ≤ ‖z‖ * a := by
      rw [abs_le] at hre_le_norm
      nlinarith [hre_le_norm.2, ha_pos]
    nlinarith [hz, ha_pos, hre_le]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · apply DifferentiableAt.neg
    apply DifferentiableAt.clog
    · first
      | exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const (a : ℂ))
      | exact (differentiableAt_const (1 : ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a : ℂ))
    · exact Or.inl hre_pos
  · exact differentiableAt_id.mul_const _


/-- Wide-radius variant (radius 4, p >= 5). -/
theorem correction_sum_differentiableOn_seven (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' p : {p : ℕ // p.Prime ∧ 7 ≤ p},
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)))
      (Metric.ball 0 (4)) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => 43 * (p : ℝ) ^ (-2*s))
  · have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 7 ≤ p}, (43 : ℝ) * (p : ℝ) ^ (-2*s) =
        43 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 43
  · intro p
    have hp3 : 7 ≤ (p : ℕ) := p.property.2
    exact correction_differentiableOn_seven (p : ℕ) hp3 s hs
  · exact Metric.isOpen_ball
  · intro p w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hp3 : 7 ≤ (p : ℕ) := p.property.2
    exact prime_correction_bound_complex_seven (p : ℕ) hp3 s hs w hw.le



/-- Wide-radius variant (radius 4, p >= 5). -/
theorem HoddTail_eq_exp_sum_seven (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 4) :
    HoddTail s z = Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 7 ≤ p},
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  have hnormsum : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
    have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => 43 * (p : ℝ) ^ (-2*s)) := by
      have h2s : -(2*s) < -1 := by linarith
      have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
        Real.summable_nat_rpow.mpr h2s
      have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
        hbase.subtype _
      have heq : ∀ p : {p : ℕ // p.Prime ∧ 7 ≤ p}, (43 : ℝ) * (p : ℝ) ^ (-2*s) =
          43 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
        intro p; ring_nf
      simp_rw [heq]
      exact hsub.mul_left 43
    apply Summable.of_nonneg_of_le
      (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => norm_nonneg _)
      (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} => by
        have hp3 : 7 ≤ (p : ℕ) := p.property.2
        exact prime_correction_bound_complex_seven (p : ℕ) hp3 s hs z hz)
      hcomp
  have hsummable : Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) :=
    Summable.of_norm hnormsum
  have hhassum := hsummable.hasSum
  have hhasprod_exp := hasProd_exp_of_hasSum hhassum
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 7 ≤ p}, Complex.exp
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z := by
    intro p
    have hp3 : 7 ≤ (p : ℕ) := p.property.2
    exact (prime_factor_eq_exp_complex_seven (p : ℕ) hp3 s hs z hz).symm
  simp only [heq] at hhasprod_exp
  have hhasprod_G2 := HoddTail_hasProd_seven s hs z hz
  exact (hhasprod_G2.unique hhasprod_exp)


/-- Wide-radius variant (radius 4, p >= 5). -/
theorem HoddTail_differentiableOn_seven (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => HoddTail s z) (Metric.ball 0 (4)) := by
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) (4), HoddTail s z = Complex.exp
      (∑' p : {p : ℕ // p.Prime ∧ 7 ≤ p},
        ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact HoddTail_eq_exp_sum_seven s hs z hz.le
  apply DifferentiableOn.congr _ heq
  exact Complex.differentiable_exp.comp_differentiableOn (correction_sum_differentiableOn_seven s hs)


/-- Htilde(s,z) = H(s,z)(1 - z 3^-s): the p = 3 pole factored out, leaving a
function analytic in |z| < 5^s.  Cauchy's estimate on |z| = R < 5 then bounds
the Taylor coefficients by M_R R^-k, which is the remainder bound of
odd-proof/PROOF.md section 5. -/
noncomputable def HoddTilde (s : ℝ) (z : ℂ) : ℂ :=
  Hodd s z * (1 - z * (((3:ℝ) ^ (-s) : ℝ) : ℂ))

/-- The p = 3 factor of Hodd, isolated. -/
theorem HoddTilde_eq (s : ℝ) (z : ℂ) :
    HoddTilde s z = Hodd s z * (1 - z * (((3:ℝ) ^ (-s) : ℝ) : ℂ)) := rfl

/-- At z = 1, s = 1: Htilde(1,1) = (1/2)(1 - 1/3) = 1/3. -/
theorem HoddTilde_one_one : HoddTilde 1 1 = (1/3 : ℂ) := by
  unfold HoddTilde
  rw [Hodd_one_one]
  rw [Real.rpow_neg_one]
  push_cast
  norm_num

/-- Cauchy's coefficient estimate, in the form odd-proof/PROOF.md section 5 uses:
if f is analytic on the closed ball of radius R and bounded by C on the
sphere, its Taylor coefficients at 0 satisfy |a_k| <= C / R^k.

This is the shape of the remainder bound; the value of C for Htilde is the
certified interval computation (odd-proof/numerics/mr_certified.py) and stays an
input, exactly as the contour sups do in the main development. -/
theorem cauchy_coeff_bound (f : ℂ → ℂ) (R C : ℝ) (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R))
    (hC : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ C) (k : ℕ) :
    ‖iteratedDeriv k f 0‖ / (Nat.factorial k) ≤ C / R ^ k := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hf hC
  have hk : (0:ℝ) < (Nat.factorial k) := by
    exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hk]
  have hRk : (0:ℝ) < R ^ k := by positivity
  calc ‖iteratedDeriv k f 0‖ ≤ (Nat.factorial k : ℝ) * C / R ^ k := h
    _ = C / R ^ k * (Nat.factorial k : ℝ) := by ring

/-- Hodd factored: the p = 3 and p = 5 Euler factors pulled out, leaving the
p >= 7 tail.  This is the form Htilde's analyticity needs -- the p = 3 factor's
pole at |z| = 3^s is what Htilde's (1 - z 3^-s) cancels, and the p = 5 factor's
pole sits at |z| = 5^s > 4. -/
theorem Hodd_factored (s : ℝ) (hs : 1 ≤ s) (z : ℂ)
    (hmul7 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p : ℝ) ^ (-s) : ℝ)) : ℂ) ^ z)) :
    Hodd s z = (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z *
      ((1 - z * (((3:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (3:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z) *
      ((1 - z * (((5:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (5:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z) *
      HoddTail s z := by
  unfold Hodd HoddTail
  set f : ℕ → ℂ := fun n =>
    (1 - z * (((n : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (n : ℝ) ^ (-s) : ℝ)) : ℂ) ^ z with hf
  have h5 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p) := by
    have := (tprod_split_five f hmul7).1
    exact this
  have hsplit5 := (tprod_split_five f hmul7).2
  have hsplit3 := (tprod_split_three f h5).2
  rw [hsplit3, hsplit5]
  norm_num [hf]
  ring

/-- The p = 3 Euler factor is differentiable on the wide disc |z| < 4.
Simpler than the general per-prime lemma: no log estimates are needed, only
that 1 - z*3^(-s) is nonvanishing there (|z*3^(-s)| < 5 / 6 at s = 1) and that
the cpow factor is entire.  The general wide lemma requires p >= 5, so the
p = 3 factor of G2C needs this separate treatment. -/
theorem prime_five_differentiableOn_four (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * ((((5 : ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ *
      ((((1 - ((5 : ℝ)) ^ (-s) : ℝ)) : ℂ)) ^ z) (Metric.ball 0 (4)) := by
  set a : ℝ := ((5 : ℝ)) ^ (-s) with ha_def
  have ha_pos : (0 : ℝ) < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 5 := by
    rw [ha_def]
    have h1 : ((5 : ℝ)) ^ (-s) ≤ ((5 : ℝ)) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rw [Real.rpow_neg_one] at h1
    norm_num at h1
    linarith
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have h1a_ne : ((((1 - a : ℝ))) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza : Norm.norm (z * ((a : ℝ) : ℂ)) < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha_pos]
    calc Norm.norm z * a < (4) * a := by
          apply mul_lt_mul_of_pos_right hz ha_pos
      _ ≤ (4) * (1 / 5) := by
          apply mul_le_mul_of_nonneg_left ha_le (by norm_num)
      _ < 1 := by norm_num
  have hne : (1 : ℂ) - z * ((a : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have := sub_eq_zero.mp hcon
    rw [← this] at hza
    simp at hza
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w * ((a : ℝ) : ℂ)) z :=
      (differentiableAt_const 1).sub (differentiableAt_id.mul (differentiableAt_const _))
    exact hinner.inv hne
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl h1a_ne)


/-- Htilde in factored form: the (1 - z 3^-s) multiplier cancels the p = 3
factor's inverse, leaving three entire prefactors, the p = 5 factor (whose
pole is at |z| = 5^s > 4) and the p >= 7 tail.  Manifestly differentiable on
ball 0 4. -/
theorem HoddTilde_factored (s : ℝ) (hs : 1 ≤ s) (z : ℂ)
    (h3ne : 1 - z * (((3:ℝ) ^ (-s) : ℝ) : ℂ) ≠ 0)
    (hmul7 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p : ℝ) ^ (-s) : ℝ)) : ℂ) ^ z)) :
    HoddTilde s z = (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z *
      (((1 - (3:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z *
      ((1 - z * (((5:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (5:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z) *
      HoddTail s z := by
  unfold HoddTilde
  rw [Hodd_factored s hs z hmul7]
  field_simp

/-- ITEM 2: Htilde is differentiable on ball 0 4.

Three factors: two entire prefactors (c^z for constant c > 0), the p = 5
Euler factor whose pole sits at |z| = 5^s >= 5, and the p >= 7 tail.  The
p = 3 pole is gone -- cancelled by Htilde's own (1 - z 3^-s). -/
theorem HoddTilde_differentiableOn (s : ℝ) (hs : 1 ≤ s)
    (hfac : ∀ z ∈ Metric.ball (0:ℂ) 4, HoddTilde s z =
      (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z * (((1 - (3:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z *
      ((1 - z * (((5:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (5:ℝ) ^ (-s) : ℝ)) : ℂ) ^ z) *
      HoddTail s z) :
    DifferentiableOn ℂ (fun z => HoddTilde s z) (Metric.ball 0 4) := by
  apply DifferentiableOn.congr _ hfac
  apply DifferentiableOn.mul
  apply DifferentiableOn.mul
  apply DifferentiableOn.mul
  · apply Differentiable.differentiableOn
    intro w
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    have hpos : (0:ℝ) < 1 - (2:ℝ) ^ (-s) := by
      have h : (2:ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      linarith
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  · apply Differentiable.differentiableOn
    intro w
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    have hpos : (0:ℝ) < 1 - (3:ℝ) ^ (-s) := by
      have h : (3:ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      linarith
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  · exact prime_five_differentiableOn_four s hs
  · exact HoddTail_differentiableOn_seven s hs

/-- The map u |-> 1 + e^(-u) sends Ioi 0 onto Ioo 1 2. -/
theorem exp_sub_image : (fun u : ℝ => 1 + Real.exp (-u)) '' Set.Ioi 0 = Set.Ioo 1 2 := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    constructor
    · have : 0 < Real.exp (-u) := Real.exp_pos _
      linarith
    · have : Real.exp (-u) < 1 := by
        rw [Real.exp_lt_one_iff]
        simpa using hu
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨-Real.log (s - 1), ?_, ?_⟩
    · simp only [Set.mem_Ioi, neg_pos]
      apply Real.log_neg <;> linarith
    · simp only
      rw [neg_neg, Real.exp_log (by linarith)]
      ring


/-- The substitution s = 1 + e^(-u) on the near-pole piece.

Maps Ioi 0 onto Ioo 1 2 with ds = -e^(-u) du, so for integrable g

    int_{Ioo 1 2} g(s) ds = int_{Ioi 0} g(1 + e^(-u)) e^(-u) du.

This is the change of variables odd-proof/PROOF.md section 2 performs; the far piece
s >= 2 is handled by the tail bound P_odd(s) <= 1.91 * 3^-s instead. -/
theorem substitution_near_pole (g : ℝ → ℝ)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 1 2) MeasureTheory.volume)
    (hgc : ContinuousOn g (Set.Ioo 1 2)) :
    ∫ s in Set.Ioo (1:ℝ) 2, g s
      = ∫ u in Set.Ioi (0:ℝ), g (1 + Real.exp (-u)) * Real.exp (-u) := by
  have hinj : Set.InjOn (fun u : ℝ => 1 + Real.exp (-u)) (Set.Ioi 0) := by
    intro a _ b _ hab
    simp only [add_right_inj] at hab
    have := Real.exp_injective hab
    linarith
  have hderiv : ∀ u ∈ Set.Ioi (0:ℝ),
      HasFDerivWithinAt (fun u : ℝ => 1 + Real.exp (-u))
        (ContinuousLinearMap.toSpanSingleton ℝ (-Real.exp (-u)))
        (Set.Ioi 0) u := by
    intro u _
    have h := ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).const_add 1
    simpa using h.hasDerivWithinAt.hasFDerivWithinAt
  rw [← exp_sub_image]
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
        MeasureTheory.volume measurableSet_Ioi hderiv hinj g]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [ContinuousLinearMap.det_toSpanSingleton, smul_eq_mul]
  rw [abs_neg, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
  ring

/-- Splitting the integral at s = 2: the near-pole piece, where the
substitution applies, and the far piece, controlled by the geometric bound
P_odd(s) <= 1.91 * 3^-s. -/
theorem integral_split_at_two (g : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 1) MeasureTheory.volume) :
    ∫ s in Set.Ioi (1:ℝ), g s
      = (∫ s in Set.Ioo (1:ℝ) 2, g s) + ∫ s in Set.Ici (2:ℝ), g s := by
  have hdisj : Disjoint (Set.Ioo (1:ℝ) 2) (Set.Ici (2:ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx2 (by simp only [Set.mem_Ici, not_le]; exact hx.2)
  have hunion : Set.Ioo (1:ℝ) 2 ∪ Set.Ici (2:ℝ) = Set.Ioi (1:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · linarith
    · intro h
      rcases lt_or_ge x 2 with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr h2
  rw [← hunion] at hint ⊢
  rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ici
    (hint.mono_set Set.subset_union_left) (hint.mono_set Set.subset_union_right)]

/-! ### Zeta's Laurent constant

Mathlib has `riemannZeta_residue_one` and `tendsto_harmonic_sub_log` but not
the constant term.  The route here, for real s > 1 only (which is all the odd
proof needs):

    zeta(s) - 1/(s-1) = sum_n [ (n+1)^-s - int_{n+1}^{n+2} x^-s dx ]

each bracket tends to 1/(n+1) - log(1 + 1/(n+1)), dominated by C/(n+1)^2, and
the limiting sum is gamma by `tendsto_harmonic_sub_log`.
-/

/-- The n-th bracket: (n+1)^-s minus the integral of x^-s over [n+1, n+2]. -/
noncomputable def zetaBracket (n : ℕ) (s : ℝ) : ℝ :=
  ((n : ℝ) + 1) ^ (-s) - ∫ x in Set.Ioc ((n : ℝ) + 1) ((n : ℝ) + 2), x ^ (-s)

/-- At s = 1 the bracket is 1/(n+1) - log((n+2)/(n+1)). -/
theorem zetaBracket_at_one (n : ℕ) :
    zetaBracket n 1 = 1 / ((n : ℝ) + 1) - (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
  unfold zetaBracket
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (n : ℝ) + 1 < (n : ℝ) + 2 := by linarith
  rw [Real.rpow_neg_one]
  congr 1
  · rw [one_div]
  · have hlog : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)
        = Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      rw [Real.log_div (by positivity) (by positivity)]
    rw [hlog, ← integral_one_div_of_pos hn1 (by linarith),
      intervalIntegral.integral_of_le (by linarith : ((n:ℝ)+1) ≤ (n:ℝ)+2)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only
    rw [Real.rpow_neg_one, one_div]

/-- For s > 1, the improper integral of x^-s over [1, inf) is 1/(s-1). -/
theorem integral_Ioi_one_rpow_neg (s : ℝ) (hs : 1 < s) :
    ∫ x in Set.Ioi (1:ℝ), x ^ (-s) = 1 / (s - 1) := by
  have h := integral_Ioi_rpow_of_lt (a := -s) (by linarith) (c := 1) (by norm_num)
  rw [h]
  rw [Real.one_rpow]
  have hne : s - 1 ≠ 0 := by intro h; linarith
  rw [show (-s + 1 : ℝ) = -(s - 1) by ring, div_neg]
  ring

/-- Ioi 1 decomposes into the unit intervals Ioc (n+1) (n+2). -/
theorem Ioi_one_eq_iUnion :
    Set.Ioi (1:ℝ) = ⋃ n : ℕ, Set.Ioc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · intro hx
    refine ⟨⌈x - 2⌉₊, ?_, ?_⟩
    · have h := Nat.le_ceil (x - 2)
      rcases Nat.eq_zero_or_pos ⌈x - 2⌉₊ with h0 | hpos
      · rw [h0]; push_cast; linarith [Nat.ceil_eq_zero.mp h0]
      · have hx2 : (0:ℝ) ≤ x - 2 := by
          by_contra hneg
          push_neg at hneg
          have : ⌈x - 2⌉₊ = 0 := Nat.ceil_eq_zero.mpr (le_of_lt hneg)
          omega
        have := Nat.ceil_lt_add_one hx2
        push_cast at this ⊢
        linarith
    · have := Nat.le_ceil (x - 2)
      push_cast
      linarith
  · rintro ⟨n, h1, _⟩
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- The telescoping: for s > 1, 1/(s-1) is the sum of the unit-interval
integrals.  Combines Ioi_one_eq_iUnion with countable additivity. -/
theorem tsum_integral_Ioc_eq (s : ℝ) (hs : 1 < s) :
    ∑' n : ℕ, (∫ x in Set.Ioc ((n : ℝ) + 1) ((n : ℝ) + 2), x ^ (-s)) = 1 / (s - 1) := by
  rw [← integral_Ioi_one_rpow_neg s hs, Ioi_one_eq_iUnion]
  rw [MeasureTheory.integral_iUnion (fun n => measurableSet_Ioc)]
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hx2
    simp only [Set.mem_Ioc] at hx hx2
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by
        have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
        linarith
      linarith [hx.2, hx2.1]
    · have : (j : ℝ) + 2 ≤ (i : ℝ) + 1 := by
        have : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
        linarith
      linarith [hx2.2, hx.1]
  · rw [← Ioi_one_eq_iUnion]
    exact integrableOn_Ioi_rpow_of_lt (by linarith : (-s : ℝ) < -1) (by norm_num)

/-- Partial sums of 1/(n+1) - log((n+2)/(n+1)) telescope to H_N - log(N+1). -/
theorem zetaBracket_partial_sum (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (1 / ((n : ℝ) + 1) - (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)))
      = (harmonic N : ℝ) - Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast [harmonic_succ]
    ring

/-- Each bracket is nonnegative: log(1 + x) <= x. -/
theorem zetaBracket_nonneg (i : ℕ) :
    0 ≤ 1 / ((i : ℝ) + 1) - (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)) := by
  have hlog : Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)
      = Real.log (1 + 1 / ((i : ℝ) + 1)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [hlog]
  have := Real.log_le_sub_one_of_pos
    (show (0:ℝ) < 1 + 1 / ((i : ℝ) + 1) by positivity)
  linarith

/-- log(N+1) - log N tends to 0. -/
theorem log_succ_sub_log_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
      Filter.atTop (nhds 0) := by
  have heq : ∀ N : ℕ, 0 < N →
      Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) = Real.log (1 + 1 / (N : ℝ)) := by
    intro N hN
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hzero : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hinner : Filter.Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) Filter.atTop (nhds 1) := by
    simpa using hzero.const_add (1 : ℝ)
  have hcomp := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hinner
  rw [Real.log_one] at hcomp
  apply Filter.Tendsto.congr' _ hcomp
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  exact (heq N hN).symm

/-- The limiting sum is gamma. -/
theorem tsum_zetaBracket_at_one :
    ∑' n : ℕ, (1 / ((n : ℝ) + 1) - (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)))
      = Real.eulerMascheroniConstant := by
  have hlim : Filter.Tendsto (fun N => (harmonic N : ℝ) - Real.log ((N : ℝ) + 1))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have hbase := tendsto_harmonic_sub_log
    have := hbase.sub log_succ_sub_log_tendsto_zero
    simpa using this
  have hsum : HasSum
      (fun n : ℕ => 1 / ((n : ℝ) + 1) - (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)))
      Real.eulerMascheroniConstant := by
    rw [hasSum_iff_tendsto_nat_of_nonneg zetaBracket_nonneg]
    simpa only [zetaBracket_partial_sum] using hlim
  exact hsum.tsum_eq

/-- Lower bound: the bracket is nonnegative, since x^-s is decreasing so the
integral over [n+1, n+2] is at most the left endpoint value. -/
theorem zetaBracket_nonneg_of_mem (n : ℕ) (s : ℝ) (hs : 1 < s) :
    0 ≤ zetaBracket n s := by
  unfold zetaBracket
  have hmono : ∀ x ∈ Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), x ^ (-s) ≤ ((n:ℝ)+1) ^ (-s) := by
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_lt hx.1) (by linarith)
  have hint : (∫ x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), x ^ (-s))
      ≤ ∫ _x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), ((n:ℝ)+1) ^ (-s) := by
    apply MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc hmono
    · apply MeasureTheory.IntegrableOn.mono_set
        (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1)
          (show (0:ℝ) < (n:ℝ)+1 by positivity))
      intro x hx
      exact hx.1
    · apply MeasureTheory.integrableOn_const
      · rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
  have hconst : (∫ _x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), ((n:ℝ)+1) ^ (-s))
      = ((n:ℝ)+1) ^ (-s) := by
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc]
    norm_num
  linarith [hint, hconst.le, hconst.ge]

/-- Upper bound: the bracket is at most (n+1)^-s - (n+2)^-s, since x^-s is
decreasing so the integral is at least the right endpoint value. -/
theorem zetaBracket_le_diff (n : ℕ) (s : ℝ) (hs : 1 < s) :
    zetaBracket n s ≤ ((n:ℝ)+1) ^ (-s) - ((n:ℝ)+2) ^ (-s) := by
  unfold zetaBracket
  have hmono : ∀ x ∈ Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), ((n:ℝ)+2) ^ (-s) ≤ x ^ (-s) := by
    intro x hx
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    exact Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith)
  have hint : (∫ _x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), ((n:ℝ)+2) ^ (-s))
      ≤ ∫ x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), x ^ (-s) := by
    apply MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc hmono
    · apply MeasureTheory.integrableOn_const
      · rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    · apply MeasureTheory.IntegrableOn.mono_set
        (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1)
          (show (0:ℝ) < (n:ℝ)+1 by positivity))
      intro x hx
      exact hx.1
  have hconst : (∫ _x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), ((n:ℝ)+2) ^ (-s))
      = ((n:ℝ)+2) ^ (-s) := by
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc]
    norm_num
  linarith [hint, hconst.le, hconst.ge]

/-- The summable dominating bound: |zetaBracket n s| <= 2/(n+1)^2 for
s in (1,2].  By the mean value theorem, (n+1)^-s - (n+2)^-s = s c^(-s-1) for
some c in (n+1,n+2), and s <= 2 with c >= n+1, s+1 >= 2 gives the bound. -/
theorem zetaBracket_bound (n : ℕ) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
    |zetaBracket n s| ≤ 2 / ((n:ℝ) + 1) ^ 2 := by
  have hlo := zetaBracket_nonneg_of_mem n s hs
  have hhi := zetaBracket_le_diff n s hs
  rw [abs_of_nonneg hlo]
  refine le_trans hhi ?_
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hab : ((n:ℝ)+1) < ((n:ℝ)+2) := by linarith
  have hderiv : ∀ x ∈ Set.Ioo ((n:ℝ)+1) ((n:ℝ)+2),
      HasDerivAt (fun y : ℝ => y ^ (-s)) (-s * x ^ (-s-1)) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    simpa using Real.hasDerivAt_rpow_const (x := x) (p := -s) (Or.inl (ne_of_gt hx0))
  have hcont : ContinuousOn (fun y : ℝ => y ^ (-s)) (Set.Icc ((n:ℝ)+1) ((n:ℝ)+2)) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    have : (0:ℝ) < x := by linarith [hx.1]
    exact ne_of_gt this
  obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope
    (fun y : ℝ => y ^ (-s)) (fun x => -s * x ^ (-s-1)) hab hcont hderiv
  simp only [add_sub_add_left_eq_sub] at hcv
  norm_num at hcv
  -- hcv : (n+2)^-s - (n+1)^-s = -s * c^(-s-1)
  have hc0 : (0:ℝ) < c := by linarith [hc.1]
  -- c^(-s-1) <= (n+1)^(-s-1) <= (n+1)^(-2)
  have h1 : c ^ (-s-1) ≤ ((n:ℝ)+1) ^ (-s-1) :=
    Real.rpow_le_rpow_of_nonpos hn1 (le_of_lt hc.1) (by linarith)
  have h2 : ((n:ℝ)+1) ^ (-s-1) ≤ ((n:ℝ)+1) ^ (-2:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have h3 : ((n:ℝ)+1) ^ (-2:ℝ) = 1 / ((n:ℝ)+1) ^ 2 := by
    rw [Real.rpow_neg (le_of_lt hn1), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast]
    rw [one_div]
  have hcpos : (0:ℝ) ≤ c ^ (-s-1) := Real.rpow_nonneg (le_of_lt hc0) _
  have hstep : s * c ^ (-s-1) ≤ 2 * c ^ (-s-1) :=
    mul_le_mul_of_nonneg_right hs2 hcpos
  have hstep2 : (2:ℝ) * c ^ (-s-1) ≤ 2 * ((n:ℝ)+1) ^ (-s-1) := by linarith
  have hstep3 : (2:ℝ) * ((n:ℝ)+1) ^ (-s-1) ≤ 2 * ((n:ℝ)+1) ^ (-2:ℝ) := by linarith
  rw [h3] at hstep3
  have hgoal : ((n:ℝ)+1) ^ (-s) - ((n:ℝ)+2) ^ (-s) = s * c ^ (-s-1) := by linarith [hcv]
  rw [hgoal]
  have : (2:ℝ) * (1 / ((n:ℝ)+1) ^ 2) = 2 / ((n:ℝ)+1) ^ 2 := by ring
  linarith [hstep, hstep2, hstep3, this]

/-- The bracket is continuous in s at s = 1 (from the right). -/
theorem zetaBracket_tendsto (n : ℕ) :
    Filter.Tendsto (fun s => zetaBracket n s) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (zetaBracket n 1)) := by
  unfold zetaBracket
  apply Filter.Tendsto.sub
  · -- (n+1)^-s is continuous in s
    have hb : ((n:ℝ)+1) ≠ 0 := by positivity
    have h : Continuous (fun s : ℝ => ((n:ℝ)+1) ^ (-s)) := by
      apply Real.continuous_const_rpow hb |>.comp continuous_neg
    exact h.continuousAt.continuousWithinAt
  · -- the integral is continuous in s by dominated convergence,
    -- dominated by x^-1 on the bounded interval [n+1, n+2]
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => ((n:ℝ)+1) ^ (-(1:ℝ)))
    · filter_upwards with s
      apply MeasureTheory.AEStronglyMeasurable.restrict
      apply Measurable.aestronglyMeasurable
      exact measurable_id.pow_const (-s)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hx0 : (0:ℝ) < x := by linarith [hx.1]
      have hs1 : (1:ℝ) < s := hs
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hx0) _)]
      calc x ^ (-s) ≤ ((n:ℝ)+1) ^ (-s) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) (le_of_lt hx.1) (by linarith)
        _ ≤ ((n:ℝ)+1) ^ (-(1:ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            linarith
    · apply MeasureTheory.integrableOn_const
      · rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : (0:ℝ) < x := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith [hx.1]
      exact ((Real.continuous_const_rpow (ne_of_gt hx0)).comp continuous_neg)
        |>.continuousAt.continuousWithinAt

/-- ZETA'S LAURENT CONSTANT.  For real s > 1,

    zeta(s) - 1/(s-1) = sum_n zetaBracket n s  ->  gamma  as s -> 1+.

The three hypotheses of dominated convergence are `summable_one_div_sq`-style
summability of 2/(n+1)^2, `zetaBracket_tendsto` for the termwise limits, and
`zetaBracket_bound` for the domination. -/
theorem tsum_zetaBracket_tendsto_gamma :
    Filter.Tendsto (fun s => ∑' n : ℕ, zetaBracket n s)
      (nhdsWithin 1 (Set.Ioc 1 2)) (nhds Real.eulerMascheroniConstant) := by
  have hbound : Summable (fun n : ℕ => 2 / ((n:ℝ) + 1) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2) := by
      have := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      apply (summable_nat_add_iff 1).mpr this |>.congr
      intro n
      push_cast
      ring
    apply (hbase.mul_left 2).congr
    intro n
    rw [mul_one_div]
  have hlim : ∀ n : ℕ, Filter.Tendsto (fun s => zetaBracket n s)
      (nhdsWithin 1 (Set.Ioc 1 2)) (nhds (zetaBracket n 1)) := by
    intro n
    apply (zetaBracket_tendsto n).mono_left
    apply nhdsWithin_mono
    exact Set.Ioc_subset_Ioi_self
  have hdom : ∀ᶠ s in nhdsWithin 1 (Set.Ioc 1 2),
      ∀ n : ℕ, ‖zetaBracket n s‖ ≤ 2 / ((n:ℝ) + 1) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs n
    rw [Real.norm_eq_abs]
    exact zetaBracket_bound n s hs.1 hs.2
  have := tendsto_tsum_of_dominated_convergence hbound hlim hdom
  simpa only [zetaBracket_at_one, tsum_zetaBracket_at_one] using this

/-- For real s > 1, zeta(s) - 1/(s-1) is exactly the sum of the brackets. -/
theorem zeta_sub_pole_eq_tsum (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1) = ∑' n : ℕ, zetaBracket n s := by
  unfold zetaBracket
  rw [← tsum_integral_Ioc_eq s hs]
  have h1 : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s)) := by
    have hb := Real.summable_nat_rpow.mpr (by linarith : (-s:ℝ) < -1)
    apply ((summable_nat_add_iff 1).mpr hb).congr
    intro n
    push_cast
    ring_nf
  have h2 : Summable (fun n : ℕ =>
      ∫ x in Set.Ioc ((n:ℝ)+1) ((n:ℝ)+2), x ^ (-s)) := by
    apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h1
    · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      intro x hx
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      exact Real.rpow_nonneg (by linarith [hx.1]) _
    · have hb := zetaBracket_nonneg_of_mem n s hs
      unfold zetaBracket at hb
      linarith
  exact (Summable.tsum_sub h1 h2).symm

/-- THE LAURENT CONSTANT, in recognisable form:

    lim_{s -> 1+} ( sum_n (n+1)^-s  -  1/(s-1) )  =  gamma.

For real s > 1 the sum is zeta(s), so this is
lim (zeta(s) - 1/(s-1)) = gamma -- the statement Mathlib is missing and the
one item 6 of the odd formalization is built on. -/
theorem zeta_laurent_constant :
    Filter.Tendsto (fun s : ℝ => (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1))
      (nhdsWithin 1 (Set.Ioc 1 2)) (nhds Real.eulerMascheroniConstant) := by
  apply Filter.Tendsto.congr' _ tsum_zetaBracket_tendsto_gamma
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (zeta_sub_pole_eq_tsum s hs.1).symm

/-! ### 6b: inverting u = log zeta(s)

From the Laurent constant, zeta(1+eps) = 1/eps + gamma + o(1), so
    u = log zeta(1+eps) = -log eps + gamma eps + o(eps),
and inverting,
    eps = e^-u + gamma e^-2u + O(e^-3u).

Only the first two orders are needed: the e^-u term gives the limit 1/2 via
H(1,1), and the e^-2u term gives the leading 2^-k via H(1,2).
-/

/-- The next order: (zeta(1+eps) - 1/eps) -> gamma, restated in eps. -/
theorem zeta_shift_laurent :
    Filter.Tendsto (fun eps : ℝ => (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))) - 1 / eps)
      (nhdsWithin 0 (Set.Ioc 0 1)) (nhds Real.eulerMascheroniConstant) := by
  have h := zeta_laurent_constant
  have hmap : Filter.Tendsto (fun eps : ℝ => 1 + eps)
      (nhdsWithin 0 (Set.Ioc 0 1)) (nhdsWithin 1 (Set.Ioc 1 2)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Filter.Tendsto (fun eps : ℝ => 1 + eps) (nhds 0) (nhds (1 + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with eps heps
      exact ⟨by linarith [heps.1], by linarith [heps.2]⟩
  have hcomp := h.comp hmap
  apply hcomp.congr
  intro eps
  simp only [Function.comp_apply]
  congr 1
  ring

/-- eps * zeta(1+eps) tends to 1, and (eps * zeta(1+eps) - 1)/eps tends to
gamma.  Both follow from the Laurent constant. -/
theorem eps_zeta_tendsto_one :
    Filter.Tendsto (fun eps : ℝ => eps * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))))
      (nhdsWithin 0 (Set.Ioc 0 1)) (nhds 1) := by
  have hL := zeta_shift_laurent
  have hid : Filter.Tendsto (fun eps : ℝ => eps) (nhdsWithin 0 (Set.Ioc 0 1)) (nhds 0) :=
    Filter.Tendsto.mono_left Filter.tendsto_id nhdsWithin_le_nhds
  have hprod := hL.mul hid
  rw [mul_zero] at hprod
  have hsum := hprod.const_add 1
  rw [add_zero] at hsum
  apply Filter.Tendsto.congr' _ hsum
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hne : eps ≠ 0 := ne_of_gt heps.1
  field_simp
  ring

/-- The inversion, in the form 6c needs.

Setting u = log zeta(1+eps), the two limits above give
    e^-u = 1/zeta(1+eps) = eps/(eps zeta(1+eps)) = eps (1 + O(eps)),
so eps = e^-u (1 + gamma e^-u + O(e^-2u)), i.e.

    eps / e^-u  ->  1     and     (eps/e^-u - 1)/e^-u  ->  gamma.

The first is `eps_zeta_tendsto_one` restated; the second is the content of
`zeta_shift_laurent`. -/
theorem eps_over_exp_tendsto_one :
    Filter.Tendsto
      (fun eps : ℝ => eps * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))))
      (nhdsWithin 0 (Set.Ioc 0 1)) (nhds 1) :=
  eps_zeta_tendsto_one

/-- The second-order term: (eps zeta(1+eps) - 1)/eps -> gamma. -/
theorem eps_zeta_second_order :
    Filter.Tendsto
      (fun eps : ℝ => (eps * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))) - 1) / eps)
      (nhdsWithin 0 (Set.Ioc 0 1)) (nhds Real.eulerMascheroniConstant) := by
  apply Filter.Tendsto.congr' _ zeta_shift_laurent
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hne : eps ≠ 0 := ne_of_gt heps.1
  field_simp

/-! ### 6c: the expansion inside the integral

FkOdd k s = [z^k] prod_{p>=3} (1 - z p^-s)^-1 = [z^k] zeta(s)^z H(s,z).

Since zeta(s)^z = e^(uz) with u = log zeta(s), the coefficient extraction gives

    FkOdd k s = sum_{j<=k} h_j(s) u^(k-j) / (k-j)!

where h_j(s) = [z^j] H(s,z).  Substituting s = 1 + e^-u and integrating over
u in (0, inf), the j-th term contributes h_j(1) times
int u^(k-j) e^(-u) / (k-j)! du = 1 at leading order -- and the corrections
come from h_j's s-dependence and from eps = e^-u (1 + gamma e^-u + ...).
-/

/-- The coefficient of z^j in H(s, ·), as a contour-free definition via the
Taylor coefficients of the analytic function Hodd s. -/
noncomputable def hCoeff (s : ℝ) (j : ℕ) : ℂ :=
  iteratedDeriv j (fun z => Hodd s z) 0 / (Nat.factorial j)

/-- h_0(1) = H(1,0) = 1: the empty product. -/
theorem hCoeff_zero_at_one : hCoeff 1 0 = 1 := by
  unfold hCoeff
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  unfold Hodd
  have hterm : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - (0:ℂ) * (((p : ℝ) ^ (-(1:ℝ)) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-(1:ℝ)) : ℝ)) : ℂ) ^ (0:ℂ) = 1 := by
    intro p
    simp
  rw [tprod_congr hterm]
  simp

/-- The Taylor series of Hodd converges to its value inside the disc of
analyticity.  Since Hodd s is differentiable on ball 0 (29/10) -- via
Hodd_factored, the p=3 and p=5 factors and HoddTail -- the series converges
for |z| < 29/10, in particular at z = 1 and z = 2.

This is the bridge between the h_j of the expansion and the values H(1,1),
H(1,2) that PROOF.md section 2 collects. -/
theorem hCoeff_hasSum (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ < 3)
    (hdiff : DifferentiableOn ℂ (fun w => Hodd s w) (Metric.ball 0 4)) :
    HasSum (fun j : ℕ => hCoeff s j * z ^ j) (Hodd s z) := by
  -- work on a closed ball of radius 3 (contains z = 1 and z = 2, sits inside 4)
  have hsub : Metric.closedBall (0:ℂ) (3:ℝ) ⊆ Metric.ball (0:ℂ) 4 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcb : DifferentiableOn ℂ (fun w => Hodd s w)
      (Metric.closedBall (0:ℂ) ((3:NNReal) : ℝ)) := by
    apply hdiff.mono
    intro w hw
    apply hsub
    simpa using hw
  have hball := hcb.hasFPowerSeriesOnBall (by norm_num)
  have hmem : z ∈ Metric.eball (0:ℂ) ((3:NNReal) : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z) |>.mpr (by simpa using hz)
  have hs := hball.hasSum hmem
  rw [zero_add] at hs
  apply hs.congr_fun
  intro n
  have hfac := hball.factorial_smul (1:ℂ) n
  unfold hCoeff
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hn : (0:ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  field_simp
  rw [← hfac]
  have hne : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [smul_eq_mul, one_pow, one_mul, nsmul_eq_mul]
  field_simp

/-- At z = 1: sum_j h_j(1) = H(1,1) = 1/2. -/
theorem hCoeff_sum_one (hdiff : DifferentiableOn ℂ (fun w => Hodd 1 w) (Metric.ball 0 4)) :
    HasSum (fun j : ℕ => hCoeff 1 j) (1/2 : ℂ) := by
  have h := hCoeff_hasSum 1 le_rfl 1 (by norm_num) hdiff
  rw [Hodd_one_one] at h
  simpa using h

/-- At z = 2: sum_j h_j(1) 2^j = H(1,2) = d. -/
theorem hCoeff_sum_two (hdiff : DifferentiableOn ℂ (fun w => Hodd 1 w) (Metric.ball 0 4)) :
    HasSum (fun j : ℕ => hCoeff 1 j * 2 ^ j) ((dConst : ℝ) : ℂ) := by
  have h := hCoeff_hasSum 1 le_rfl 2 (by norm_num) hdiff
  rw [Hodd_one_two] at h
  exact h

/-! ### 6c: the coefficient extraction

    sum_k FkOdd k s * z^k = prod_{p>=3} (1 - z p^-s)^-1 = zeta(s)^z * Hodd s z
                          = e^(u z) * Hodd s z,      u = log zeta(s)

Extracting z^k from the product of e^(uz) = sum_m u^m z^m / m! and
Hodd s z = sum_j h_j(s) z^j gives the convolution

    FkOdd k s = sum_{j<=k} h_j(s) * u^(k-j) / (k-j)!.

This is the odd analogue of Fk_expansion_manu.  It is what turns the Taylor
coefficients h_j into the k-dependence that the theorem needs.
-/

/-- u(s) = log zeta(s), for real s > 1. -/
noncomputable def uOf (s : ℝ) : ℝ := Real.log (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))

/-- The odd generating function as a sum over odd n: sum_{n odd} z^Omega(n) n^-s.
Same shape as the main development's tsum of zOmegaHom, restricted to odd n. -/
noncomputable def zOmegaOdd (s : ℝ) (z : ℂ) : ℂ :=
  ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}, z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s : ℂ)))

/-- The derivative bound, restricted to the odd index set: a subfamily of a
summable nonnegative family. -/
theorem deriv_bound_summable_odd (s : ℝ) (hs : 1 < s) (j : ℕ)
    (r0 r : ℝ) (hr01 : 1 ≤ r0) (hr0r : r0 < r)
    (hr0 : 0 ≤ r) (hr3 : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) (hr2 : r < (2 : ℝ) ^ s) :
    Summable (fun n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} =>
      ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n - j) * (((n : ℕ) : ℝ) ^ (-s))) :=
  (deriv_bound_summable s hs j r0 r hr01 hr0r hr0 hr3 hr2).subtype _

/-- Termwise differentiation for the odd sum.  The per-term lemmas
(iteratedDeriv_term_zero, _differentiable, _bound) are stated for a single n
and so apply unchanged; only the summability of the bound changes index set. -/
theorem iteratedDeriv_tsum_eq_odd (s : ℝ) (hs : 1 < s) (r0 r : ℝ)
    (hr01 : 1 ≤ r0) (hr0r : r0 < r) (hr0 : 0 ≤ r)
    (hr3 : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) (hr2 : r < (2 : ℝ) ^ s) :
    ∀ j : ℕ, ∀ w : ℂ, Norm.norm w < r0 →
      iteratedDeriv j (fun z : ℂ =>
        ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}, zOmegaHom s z (n : ℕ)) w
        = ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
            iteratedDeriv j (fun z : ℂ => zOmegaHom s z (n : ℕ)) w := by
  intro j
  induction j with
  | zero =>
    intro w hw
    simp only [iteratedDeriv_zero]
  | succ J IH =>
    intro w hw
    have hball : IsOpen (Metric.ball (0 : ℂ) r0) := Metric.isOpen_ball
    have hwmem : w ∈ Metric.ball (0 : ℂ) r0 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw
    have hbound := deriv_bound_summable_odd s hs J r0 r hr01 hr0r hr0 hr3 hr2
    have hdiff : ∀ n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}, DifferentiableOn ℂ
        (fun v : ℂ => iteratedDeriv J (fun z : ℂ => zOmegaHom s z (n : ℕ)) v)
        (Metric.ball (0 : ℂ) r0) := by
      intro n
      have hn : (n : ℕ) ≠ 0 := by have := n.2.1; omega
      exact (iteratedDeriv_term_differentiable s n hn J).differentiableOn
    have hle : ∀ (n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}) (v : ℂ), v ∈ Metric.ball (0 : ℂ) r0 →
        Norm.norm (iteratedDeriv J (fun z : ℂ => zOmegaHom s z (n : ℕ)) v)
          ≤ ((bigOmega (n : ℕ) : ℕ) : ℝ) ^ J * r0 ^ (bigOmega (n : ℕ) - J) * (((n : ℕ) : ℝ) ^ (-s)) := by
      intro n v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      have hn : (n : ℕ) ≠ 0 := by have := n.2.1; omega
      exact iteratedDeriv_term_bound s hs r0 (by linarith : (0 : ℝ) < r0) J n hn v (le_of_lt hv)
    have hmain := Complex.hasSum_deriv_of_summable_norm hbound hdiff hball hle hwmem
    have hIHball : (fun v : ℂ => iteratedDeriv J (fun z : ℂ => ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}, zOmegaHom s z (n : ℕ)) v)
        =ᶠ[nhds w] fun v : ℂ => ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}, iteratedDeriv J (fun z : ℂ => zOmegaHom s z (n : ℕ)) v := by
      filter_upwards [hball.mem_nhds hwmem] with v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      exact IH v hv
    rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hIHball, ← hmain.tsum_eq]
    apply tsum_congr
    intro n
    rw [iteratedDeriv_succ]


/-- FkOdd is the k-th Taylor coefficient of the odd generating function.
Mirrors Fk_eq_coeff_tsum: termwise differentiation, then each term's k-th
derivative at 0 picks out Omega(n) = k (iteratedDeriv_term_at_zero is stated
per-n and so applies unchanged). -/
theorem FkOdd_eq_coeff_tsum (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) :
    ((FkOdd k s : ℝ) : ℂ)
      = iteratedDeriv k (fun z => zOmegaOdd s z) 0 / (Nat.factorial k : ℂ) := by
  obtain ⟨ r, hrgt, hr3, hr2 ⟩ := exists_radius_gap s hs
  unfold zOmegaOdd
  have hzz : ∀ z : ℂ, (∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
      z ^ (bigOmega (n : ℕ)) * (((n : ℕ) : ℂ) ^ (-(s : ℂ))))
      = ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}, zOmegaHom s z (n : ℕ) := by
    intro z
    apply tsum_congr
    intro n
    have hn : (n : ℕ) ≠ 0 := by have := n.2.1; omega
    unfold zOmegaHom
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hn]
  simp only [hzz]
  rw [iteratedDeriv_tsum_eq_odd s hs (3/2) r (by norm_num) hrgt (by linarith) hr3 hr2
    k 0 (by norm_num)]
  have hcollapse : (∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
      iteratedDeriv k (fun z : ℂ => zOmegaHom s z (n : ℕ)) 0)
      = ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
        (if bigOmega (n : ℕ) = k then (Nat.factorial k : ℂ) * ((((n : ℕ) : ℂ)) ^ (-(s : ℂ))) else 0) := by
    apply tsum_congr
    intro n
    exact iteratedDeriv_term_at_zero s k hk (n : ℕ)
  rw [hcollapse]
  have hfac : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpull : (∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
      (if bigOmega (n : ℕ) = k then (Nat.factorial k : ℂ) * ((((n : ℕ) : ℂ)) ^ (-(s : ℂ))) else 0))
      = (Nat.factorial k : ℂ) * ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
        (if bigOmega (n : ℕ) = k then ((((n : ℕ) : ℂ)) ^ (-(s : ℂ))) else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases h : bigOmega (n : ℕ) = k
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hpull]
  field_simp
  unfold FkOdd
  rw [Complex.ofReal_tsum]
  -- both sides are sums over {3<=n, odd}; on the left the Omega=k condition is
  -- in the subtype, on the right it is an indicator
  -- reindex: the triple-condition subtype is equivalent to the {Omega = k}
  -- sub-subtype of the odd subtype
  let hequiv : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}
      ≃ {n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} // bigOmega (n : ℕ) = k} :=
    { toFun := fun a => ⟨⟨a.1, by omega, a.2.2.1⟩, a.2.2.2⟩,
      invFun := fun b => ⟨b.1.1, by
        have h1 := b.1.2.1
        have hodd := b.1.2.2
        have hk := b.2
        have hO1 : bigOmega 1 = 0 := by unfold bigOmega; simp
        rcases Nat.lt_or_ge (b.1.1) 3 with hlt | hge
        · exfalso
          interval_cases h : (b.1.1 : ℕ)
          · rw [hO1] at hk; omega
          · exact hodd ⟨1, rfl⟩
        · exact hge, b.1.2.2, b.2⟩,
      left_inv := fun a => rfl,
      right_inv := fun b => rfl }
  have hstep : (∑' a : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k},
      ((((a : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      = ∑' b : {n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} // bigOmega (n : ℕ) = k},
        (((((b : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}) : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) :=
    by
      rw [← hequiv.tsum_eq
        (fun b : {n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} // bigOmega (n : ℕ) = k} =>
          (((((b : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)}) : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))]
      apply tsum_congr
      intro c
      simp only [hequiv, Equiv.coe_fn_mk]
  rw [hstep]
  have hrhs : (∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
      (if bigOmega (n : ℕ) = k then ((((n : ℕ) : ℂ)) ^ (-(s : ℂ))) else 0))
      = ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)},
        Set.indicator {m : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} | bigOmega (m : ℕ) = k}
          (fun m => ((((m : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) n := by
    apply tsum_congr
    intro n
    by_cases h : bigOmega (n : ℕ) = k
    · have hmem : n ∈ {m : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} | bigOmega (m : ℕ) = k} := h
      rw [if_pos h, Set.indicator_of_mem hmem]
      rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    · have hnmem : n ∉ {m : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} | bigOmega (m : ℕ) = k} := h
      rw [if_neg h, Set.indicator_of_notMem hnmem]
  rw [hrhs, ← tsum_subtype
    {m : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} | bigOmega (m : ℕ) = k}
    (fun m : {n : ℕ // 1 ≤ n ∧ ¬ (2 ∣ n)} => ((((m : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))]
  rfl

/-- Every n >= 1 factors uniquely as 2^a * m with m odd: the 2-adic valuation
and the odd part.  This is the bijection underlying zOmega_split_two. -/
noncomputable def twoAdicSplit : {n : ℕ // 1 ≤ n} ≃ ℕ × {m : ℕ // 1 ≤ m ∧ ¬ (2 ∣ m)} where
  toFun n := (n.1.factorization 2,
    ⟨n.1 / 2 ^ (n.1.factorization 2), by
      constructor
      · have h := Nat.ordProj_mul_ordCompl_eq_self n.1 2
        rcases Nat.eq_zero_or_pos (n.1 / 2 ^ (n.1.factorization 2)) with hz | hp
        · rw [hz, mul_zero] at h
          omega
        · exact hp
      · exact Nat.not_dvd_ordCompl Nat.prime_two (by omega)⟩)
  invFun p := ⟨2 ^ p.1 * p.2.1, by
    have hm := p.2.2.1
    have h2 : 1 ≤ 2 ^ p.1 := Nat.one_le_two_pow
    calc 1 = 1 * 1 := by ring
      _ ≤ 2 ^ p.1 * p.2.1 := Nat.mul_le_mul h2 hm⟩
  left_inv := by
    intro n
    apply Subtype.ext
    exact Nat.ordProj_mul_ordCompl_eq_self n.1 2
  right_inv := by
    intro q
    have hm0 : q.2.1 ≠ 0 := by have := q.2.2.1; omega
    have hmodd : ¬ (2 ∣ q.2.1) := q.2.2.2
    have hv2m : (q.2.1).factorization 2 = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left; exact hmodd
    have hpow0 : (2 ^ q.1 : ℕ) ≠ 0 := by positivity
    have hfac : (2 ^ q.1 * q.2.1).factorization 2 = q.1 := by
      rw [Nat.factorization_mul hpow0 hm0]
      simp only [Finsupp.coe_add, Pi.add_apply, hv2m, add_zero]
      rw [Nat.Prime.factorization_pow Nat.prime_two]
      simp
    apply Prod.ext
    · simp only
      exact hfac
    · apply Subtype.ext
      simp only
      rw [hfac]
      exact Nat.mul_div_cancel_left _ (by positivity)

/-- Omega is additive on the 2-adic split: Omega(2^a * m) = a + Omega(m). -/
theorem bigOmega_two_pow_mul (a m : ℕ) (hm : 1 ≤ m) :
    bigOmega (2 ^ a * m) = a + bigOmega m := by
  unfold bigOmega
  have hpow : (2 ^ a : ℕ) ≠ 0 := by positivity
  have hm0 : m ≠ 0 := by omega
  rw [Nat.factorization_mul hpow hm0]
  rw [Finsupp.sum_add_index']
  · congr 1
    rw [Nat.Prime.factorization_pow Nat.prime_two]
    simp
  · intro p
    rfl
  · intro p b1 b2
    rfl

/-- The summand transforms correctly under the split. -/
theorem zOmega_split_summand (s : ℝ) (z : ℂ) (a m : ℕ) (hm : 1 ≤ m) :
    z ^ (bigOmega (2 ^ a * m)) * (((2 ^ a * m : ℕ) : ℂ) ^ (-(s : ℂ)))
      = (z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ a * (z ^ (bigOmega m) * ((m : ℂ) ^ (-(s : ℂ)))) := by
  rw [bigOmega_two_pow_mul a m hm]
  rw [pow_add]
  push_cast
  have hsplit : ((2:ℂ) ^ a * (m : ℂ)) ^ (-(s : ℂ))
      = (((2:ℝ) ^ (-s) : ℝ) : ℂ) ^ a * ((m : ℂ) ^ (-(s : ℂ))) := by
    have h2a : ((2:ℂ) ^ a) = (((2 ^ a : ℝ)) : ℂ) := by push_cast; ring
    have hmR : ((m : ℂ)) = (((m : ℝ)) : ℂ) := by push_cast; ring
    rw [h2a, hmR, ← Complex.ofReal_mul]
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cpow (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast (2:ℝ) a, ← Real.rpow_mul (by norm_num)]
    have hR : (((2:ℝ) ^ (-s) : ℝ) : ℂ) ^ a = ((((2:ℝ) ^ (-s)) ^ a : ℝ) : ℂ) := by
      push_cast; ring
    rw [hR]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg m), ← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_natCast ((2:ℝ) ^ (-s)) a, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hsplit]
  ring

/-- The p = 2 factor relates the odd sum to the full sum:
every n factors uniquely as 2^a * m with m odd, so
    sum_n z^Omega(n) n^-s = (sum_a (z 2^-s)^a) * (sum_{m odd} z^Omega(m) m^-s). -/
theorem zOmega_split_two (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : ‖z‖ < 2 ^ s)
    (hsum : Summable (fun n : ℕ => ‖zOmegaHom s z n‖)) :
    (∑' n : ℕ, zOmegaHom s z n)
      = (1 - z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * zOmegaOdd s z := by
  -- the n = 0 term vanishes, so the sum is over n >= 1
  have hzero : ∀ z : ℂ, zOmegaHom s z 0 = 0 := by
    intro z; unfold zOmegaHom; simp
  -- reindex n >= 1 as (a, m) with m odd via twoAdicSplit
  have hreindex : (∑' n : {n : ℕ // 1 ≤ n}, zOmegaHom s z (n : ℕ))
      = ∑' q : ℕ × {m : ℕ // 1 ≤ m ∧ ¬ (2 ∣ m)},
        (z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ q.1 *
          (z ^ (bigOmega (q.2 : ℕ)) * (((q.2 : ℕ) : ℂ) ^ (-(s : ℂ)))) := by
    rw [← twoAdicSplit.tsum_eq
      (fun q : ℕ × {m : ℕ // 1 ≤ m ∧ ¬ (2 ∣ m)} =>
        (z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ q.1 *
          (z ^ (bigOmega (q.2 : ℕ)) * (((q.2 : ℕ) : ℂ) ^ (-(s : ℂ)))))]
    apply tsum_congr
    intro n
    have hn1 : 1 ≤ (n : ℕ) := n.2
    have hne : (n : ℕ) ≠ 0 := by omega
    unfold zOmegaHom
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hne]
    simp only [twoAdicSplit, Equiv.coe_fn_mk]
    rw [← zOmega_split_summand s z ((n : ℕ).factorization 2)
      ((n : ℕ) / 2 ^ ((n : ℕ).factorization 2)) (by
        rcases Nat.eq_zero_or_pos ((n : ℕ) / 2 ^ ((n : ℕ).factorization 2)) with hz | hp
        · have h := Nat.ordProj_mul_ordCompl_eq_self (n : ℕ) 2
          rw [hz, mul_zero] at h
          omega
        · exact hp)]
    rw [Nat.ordProj_mul_ordCompl_eq_self]
  -- the double sum factors: geometric in a, the odd sum in m
  have hgeom : (∑' a : ℕ, (z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ a)
      = (1 - z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    apply tsum_geometric_of_norm_lt_one
    rw [norm_mul]
    have h2 : ‖(((2 : ℝ) ^ (-s) : ℝ) : ℂ)‖ = (2 : ℝ) ^ (-s) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h2]
    have hlt : (2 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hzlt : ‖z‖ < 2 ^ s := hz
    have h2s : ((2 : ℝ) ^ (-s)) = ((2 : ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    rw [h2s]
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hzlt
  -- the double sum factors
  have hprod : (∑' q : ℕ × {m : ℕ // 1 ≤ m ∧ ¬ (2 ∣ m)},
      (z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ q.1 *
        (z ^ (bigOmega (q.2 : ℕ)) * (((q.2 : ℕ) : ℂ) ^ (-(s : ℂ)))))
      = (∑' a : ℕ, (z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ a) *
        (∑' m : {m : ℕ // 1 ≤ m ∧ ¬ (2 ∣ m)},
          z ^ (bigOmega (m : ℕ)) * (((m : ℕ) : ℂ) ^ (-(s : ℂ)))) := by
    have hnlt : ‖z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)‖ < 1 := by
      rw [norm_mul]
      have h2 : ‖(((2 : ℝ) ^ (-s) : ℝ) : ℂ)‖ = (2 : ℝ) ^ (-s) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h2, Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_lt_one (by positivity)]
      exact hz
    have hgs : Summable (fun a : ℕ => ‖(z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ a‖) := by
      simp only [norm_pow]
      exact summable_geometric_of_lt_one (by positivity) hnlt
    have hos : Summable (fun m : {m : ℕ // 1 ≤ m ∧ ¬ (2 ∣ m)} =>
        ‖z ^ (bigOmega (m : ℕ)) * (((m : ℕ) : ℂ) ^ (-(s : ℂ)))‖) := by
      have hsub := hsum.subtype {m : ℕ | 1 ≤ m ∧ ¬ (2 ∣ m)}
      apply hsub.congr
      intro m
      have hmem : (1 : ℕ) ≤ m.val ∧ ¬ (2 ∣ m.val) := m.2
      have hm0 : m.val ≠ 0 := by
        have := hmem.1
        omega
      unfold zOmegaHom
      simp only [Function.comp_apply, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      rw [if_neg hm0]
    exact (tsum_mul_tsum_of_summable_norm hgs hos).symm
  -- the n = 0 term vanishes, so the full sum is the sum over n >= 1
  have hdrop : (∑' n : ℕ, zOmegaHom s z n)
      = ∑' n : {n : ℕ // 1 ≤ n}, zOmegaHom s z (n : ℕ) := by
    show (∑' n : ℕ, zOmegaHom s z n)
      = ∑' n : ({n : ℕ | 1 ≤ n} : Set ℕ), zOmegaHom s z (n : ℕ)
    rw [tsum_subtype {n : ℕ | 1 ≤ n} (fun n : ℕ => zOmegaHom s z n)]
    apply tsum_congr
    intro n
    by_cases hn : 1 ≤ n
    · have hmem : n ∈ ({n : ℕ | 1 ≤ n} : Set ℕ) := hn
      rw [Set.indicator_of_mem hmem]
    · have hnmem : n ∉ ({n : ℕ | 1 ≤ n} : Set ℕ) := hn
      rw [Set.indicator_of_notMem hnmem]
      have hz0 : n = 0 := by omega
      rw [hz0, hzero]
  rw [hdrop, hreindex, hprod, hgeom]
  rfl

/-- Assembling the Euler product for the odd part.  Needs, as hypotheses, the
absolute summability that `zOmega_eulerProduct` also requires, and the
multipliability of the p >= 3 family. -/
theorem zOmegaOdd_eq_euler' (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : ‖z‖ < 2 ^ s)
    (hsum : Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - zOmegaHom s z (p : ℕ))⁻¹)) :
    zOmegaOdd s z = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - zOmegaHom s z (p : ℕ))⁻¹ := by
  have hfull := zOmega_eulerProduct s hs z hsum
  have hsplit2 := (tprod_split_two (fun n : ℕ => (1 - zOmegaHom s z n)⁻¹) hmul3).2
  have hsplitOdd := zOmega_split_two s hs z hz hsum
  have hfull' : (∏' p : {p : ℕ // p.Prime}, (1 - zOmegaHom s z (p : ℕ))⁻¹)
      = ∑' n : ℕ, zOmegaHom s z n := hfull
  rw [hsplit2] at hfull'
  replace hfull := hfull'
  rw [hsplitOdd] at hfull
  have h2 : zOmegaHom s z 2 = z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ) := by
    unfold zOmegaHom
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg (by norm_num : (2:ℕ) ≠ 0)]
    have hO2 : bigOmega 2 = 1 := by
      unfold bigOmega
      rw [Nat.Prime.factorization Nat.prime_two]
      simp
    rw [hO2, pow_one]
    congr 1
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by norm_num)]
    norm_num
  rw [h2] at hfull
  have hne : (1 - z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)) ≠ 0 := by
    intro hzero0
    have hnorm : ‖z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ)‖ = 1 := by
      have : z * (((2 : ℝ) ^ (-s) : ℝ) : ℂ) = 1 := by linear_combination -hzero0
      rw [this, norm_one]
    rw [norm_mul] at hnorm
    have hb : ‖(((2 : ℝ) ^ (-s) : ℝ) : ℂ)‖ = (2 : ℝ) ^ (-s) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hb, Real.rpow_neg (by norm_num), ← div_eq_mul_inv] at hnorm
    have := (div_eq_one_iff_eq (by positivity)).mp hnorm
    linarith [hz, this.le, this.ge]
  field_simp at hfull
  simp only [← one_div]
  exact hfull.symm

/-- zeta(s)^z = exp(u z) with u = log zeta(s), so its j-th derivative at 0 is u^j. -/
theorem iteratedDeriv_zeta_cpow (s : ℝ) (hs : 1 < s) (j : ℕ) :
    iteratedDeriv j (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0 = ((uOf s : ℝ) : ℂ) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z))
        = fun z : ℂ => ((uOf s : ℝ) : ℂ) * Complex.exp ((uOf s : ℂ) * z) := by
      funext w
      simp [Complex.deriv_exp, mul_comm]
    rw [hderiv]
    rw [iteratedDeriv_const_mul]
    · rw [ih]
      ring
    · apply ContDiff.contDiffAt
      exact Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)

/-- THE CONVOLUTION (6c step 2, second half).

By Leibniz applied to zOmegaOdd s = exp(u ·) * Hodd s, the k-th Taylor
coefficient is the convolution of u^j/j! with h_j. -/
theorem FkOdd_convolution (k : ℕ) (s : ℝ) (hs : 1 < s)
    (hfac : ∀ z ∈ Metric.ball (0:ℂ) 2, zOmegaOdd s z
      = Complex.exp ((uOf s : ℂ) * z) * Hodd s z)
    (hcd1 : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0) :
    iteratedDeriv k (fun z => zOmegaOdd s z) 0 / (Nat.factorial k : ℂ)
      = ∑ j ∈ Finset.range (k + 1),
          hCoeff s j * ((uOf s : ℝ) : ℂ) ^ (k - j) / (Nat.factorial (k - j)) := by
  have hfun : (fun z => zOmegaOdd s z)
      =ᶠ[nhds (0:ℂ)] (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) * (fun z : ℂ => Hodd s z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ) ∈ Metric.ball (0:ℂ) 2)]
      with z hzmem
    exact hfac z hzmem
  rw [hfun.iteratedDeriv_eq, iteratedDeriv_mul hcd1 hcd2]
  rw [Finset.sum_div]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hnorm : k + 1 - 1 - i = k - i := by omega
  rw [hnorm]
  rw [iteratedDeriv_zeta_cpow s hs (k - i)]
  have hsub : k - (k - i) = i := by omega
  rw [hsub]
  unfold hCoeff
  rw [Nat.choose_symm hik]
  have hkey : (k.choose i : ℂ) * (Nat.factorial i : ℂ) * (Nat.factorial (k - i) : ℂ)
      = (Nat.factorial k : ℂ) := by
    have := Nat.choose_mul_factorial_mul_factorial hik
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) this
  have hi0 : (Nat.factorial i : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hki0 : (Nat.factorial (k - i) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k - i)
  have hk0 : (Nat.factorial k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  linear_combination (↑(uOf s) ^ (k - i) * iteratedDeriv i (fun z => Hodd s z) 0) * hkey

/-- The bracket is 1: zeta(s) (1 - 2^-s) prod_{p>=3}(1 - p^-s) = 1. -/
theorem zeta_two_cFac_eq_one (s : ℝ) (hs : 1 < s) :
    ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) : ℝ) : ℂ) * ((1 - (2:ℝ) ^ (-s) : ℝ) : ℂ)
      * ((cFac s : ℝ) : ℂ)⁻¹ = 1 := by
  have hz := cFac_eq_zeta s hs
  have hser : ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [one_div, ← Complex.cpow_neg]
    have hb : (0:ℝ) ≤ ((n:ℝ) + 1) := by positivity
    have hoc := Complex.ofReal_cpow hb (-s)
    push_cast at hoc
    push_cast
    exact hoc
  have h2 : ((1 - (2:ℝ) ^ (-s) : ℝ) : ℂ) = 1 - ((2 : ℂ)) ^ (-(s : ℂ)) := by
    have hb : (((2:ℝ) ^ (-s) : ℝ) : ℂ) = ((2 : ℂ)) ^ (-(s : ℂ)) := by
      have := Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2) (-s)
      rw [show ((2:ℝ) : ℂ) = (2 : ℂ) by norm_num] at this
      rw [show (((-s : ℝ)) : ℂ) = -(s : ℂ) by push_cast; ring] at this
      exact this
    push_cast [hb]
    ring
  rw [hser, h2, ← hz]
  have hne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (cFac_pos s hs)
  field_simp

/-- The factorization zOmegaOdd s z = exp(u(s) z) * Hodd s z.

Unfolding Hodd, the p >= 3 product cancels and what remains is
    1 = [zeta(s) (1 - 2^-s) * prod_{p>=3}(1 - p^-s)]^z
which holds because zeta(s)(1 - 2^-s) = cFac s (cFac_eq_zeta in the main
development) and cFac s = prod_{p>=3}(1 - p^-s)^-1 by definition. -/
theorem zOmegaOdd_factor (s : ℝ) (hs : 1 < s) (z : ℂ) (hz2 : ‖z‖ ≤ 2)
    (hz : ‖z‖ < 2 ^ s)
    (hsum : Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - zOmegaHom s z (p : ℕ))⁻¹)) :
    zOmegaOdd s z = Complex.exp ((uOf s : ℂ) * z) * Hodd s z := by
  rw [zOmegaOdd_eq_euler' s hs z hz hsum hmul3]
  unfold Hodd
  -- exp(u z) = (zeta s)^z since u = log (zeta s)
  have hzpos : (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
    have hsummable : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s)) := by
      have hb := Real.summable_nat_rpow.mpr (by linarith : (-s:ℝ) < -1)
      apply ((summable_nat_add_iff 1).mpr hb).congr
      intro n
      push_cast
      ring_nf
    have hterm : (0:ℝ) < ((0:ℕ) + 1 : ℝ) ^ (-s) := by norm_num
    have hle := hsummable.le_tsum 0 (fun n _ => by positivity)
    calc (0:ℝ) < ((0:ℝ) + 1) ^ (-s) := by norm_num
      _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by simpa using hle
  have hexp : Complex.exp ((uOf s : ℂ) * z)
      = (((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) : ℝ)) : ℂ) ^ z := by
    unfold uOf
    rw [Complex.cpow_def_of_ne_zero (by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hzpos)]
    congr 1
    rw [← Complex.ofReal_log (le_of_lt hzpos)]
  rw [hexp]
  have hc : 0 < cFac s := cFac_pos s hs
  have hmulR := cFac_multipliable s hs
  have hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ := by
    intro p
    obtain ⟨h3, hp⟩ := cFac_factor_le_third s hs p
    exact inv_pos.mpr (by linarith)
  have hlogR := cFac_log_summable s hs
  have hreg := (tail_regroup_hasProd s hs z hz2 hc hmulR hposR hlogR).tprod_eq
  have hzo : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      zOmegaHom s z (p : ℕ) = z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    have hp0 : ((p : ℕ) : ℕ) ≠ 0 := by
      have := p.2.2
      omega
    unfold zOmegaHom
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hp0]
    have hO : bigOmega (p : ℕ) = 1 := by
      unfold bigOmega
      rw [Nat.Prime.factorization p.2.1]
      simp
    rw [hO, pow_one]
    congr 1
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp only [hzo]
  rw [hreg]
  -- (cFac s)^z = (zeta s)^z (1 - 2^-s)^z, and Hodd = (1-2^-s)^z * G2C
  have hcz : ((cFac s : ℝ) : ℂ) ^ z
      = (((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) : ℝ)) : ℂ) ^ z
        * ((1 - (2:ℝ) ^ (-s) : ℝ) : ℂ) ^ z := by
    have hzt := zeta_two_cFac_eq_one s hs
    have hcne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hc
    have hbase : ((cFac s : ℝ) : ℂ)
        = (((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) : ℝ)) : ℂ) * ((1 - (2:ℝ) ^ (-s) : ℝ) : ℂ) := by
      field_simp at hzt
      linear_combination -hzt
    have hb2 : (0:ℝ) ≤ 1 - (2:ℝ) ^ (-s) := by
      have h2 : (2:ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      linarith
    rw [hbase]
    exact Complex.mul_cpow_ofReal_nonneg (le_of_lt hzpos) hb2 z
  rw [hcz]
  rw [reg_tprod_eq_G2C s (le_of_lt hs) z hz2]
  ring

/-- 6c COMPLETE: FkOdd is the convolution of the h_j with u^m/m!.

Composes FkOdd_eq_coeff_tsum (the arithmetic sum is a Taylor coefficient),
zOmegaOdd_factor (the generating function factors as exp(uz) * Hodd), and
FkOdd_convolution (Leibniz). -/
theorem FkOdd_expansion' (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s)
    (hsum : ∀ z : ℂ, ‖z‖ ≤ 2 → Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : ∀ z : ℂ, ‖z‖ ≤ 2 → Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - zOmegaHom s z (p : ℕ))⁻¹))
    (hcd1 : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0) :
    ((FkOdd k s : ℝ) : ℂ) = ∑ j ∈ Finset.range (k + 1),
      hCoeff s j * ((uOf s : ℝ) : ℂ) ^ (k - j) / (Nat.factorial (k - j)) := by
  rw [FkOdd_eq_coeff_tsum k hk s hs]
  apply FkOdd_convolution k s hs _ hcd1 hcd2
  intro z hzmem
  rw [Metric.mem_ball, dist_zero_right] at hzmem
  have hz2s : ‖z‖ < 2 ^ s := by
    have : (2:ℝ) < 2 ^ s := by
      calc (2:ℝ) = 2 ^ (1:ℝ) := by norm_num
        _ < 2 ^ s := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    linarith
  exact zOmegaOdd_factor s hs z (le_of_lt hzmem) hz2s
    (hsum z (le_of_lt hzmem)) (hmul3 z (le_of_lt hzmem))


/-! ### 6c step 3: integrating the expansion

    f_k^odd = int_{Ioi 1} FkOdd k s ds
            = int_{Ioi 0} FkOdd k (1 + e^-u) e^-u du       [substitution, item 5]

and FkOdd k (1+e^-u) = sum_j h_j(1+e^-u) u_*^(k-j)/(k-j)! with u_* = log zeta.

At leading order u_* = u and h_j(1+e^-u) = h_j(1), so the j-th term integrates
against int u^(k-j) e^-u /(k-j)! du = 1, giving sum_j h_j(1) = H(1,1) = 1/2.
The e^-2u correction gives the beta 2^-k term via
int u^i e^(-2u) du = i!/2^(i+1).

The Gamma evaluations are already in the main development:
integral_exp_neg_mul_pow, integral_pow_exp_neg_two_mul,
integral_pow_exp_neg_three_mul. -/

/-- The leading-order integral: int_{Ioi 0} u^m e^-u / m! du = 1. -/
theorem gamma_normalised (m : ℕ) :
    (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ m) / (Nat.factorial m : ℝ) = 1 := by
  rw [integral_exp_neg_mul_pow m]
  have : (Nat.factorial m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-- The second-order integral: int_{Ioi 0} u^m e^(-2u) / m! du = 2^-(m+1).
This is where the 2^-k in f_k^odd - 1/2 comes from -- note it arises from the
integral, not from any prime, which is why it survives removing p = 2. -/
theorem gamma_normalised_two (m : ℕ) :
    (∫ u in Set.Ioi (0:ℝ), u ^ m * Real.exp (-(2 * u))) / (Nat.factorial m : ℝ)
      = 1 / 2 ^ (m + 1) := by
  rw [integral_pow_exp_neg_two_mul m]
  have hne : (Nat.factorial m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-- The third-order integral, for the remainder: int u^m e^(-3u)/m! = 3^-(m+1). -/
theorem gamma_normalised_three (m : ℕ) :
    (∫ u in Set.Ioi (0:ℝ), u ^ m * Real.exp (-(3 * u))) / (Nat.factorial m : ℝ)
      = 1 / 3 ^ (m + 1) := by
  rw [integral_pow_exp_neg_three_mul m]
  have hne : (Nat.factorial m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-! ### 6b: the uniform estimate

The two limits (eps_zeta_tendsto_one, eps_zeta_second_order) say

    eps * zeta(1+eps) = 1 + gamma eps + o(eps).

For step 3 we need this as a BOUND on a definite range, not a limit:
there are C and eps0 > 0 with

    |eps zeta(1+eps) - 1 - gamma eps| <= C eps^2   for 0 < eps <= eps0.

Substituting eps = e^-u, this controls u_* = log zeta(1+e^-u) against u, and
the error enters the integrals at order e^-3u -- the third Gamma evaluation.
-/

/-! ### The second-order bound, via the completed zeta

Mathlib gives:
  riemannZeta_def_of_ne_zero : s != 0 -> zeta s = completedRiemannZeta s / Gammaℝ s
  completedRiemannZeta_eq    : Λ s = Λ₀ s - 1/s - 1/(1-s)
  differentiable_completedZeta₀ : Λ₀ entire
  Gammaℝ_one : Gammaℝ 1 = 1,  Gammaℝ_ne_zero_of_re_pos

So near s = 1 the only pole of zeta comes from -1/(1-s) = 1/(s-1) divided by
Gammaℝ, and since Gammaℝ 1 = 1 the residue is 1.  Hence

    zeta s - 1/(s-1)

extends differentiably across s = 1 -- WITHOUT naming the Stieltjes constant.
Differentiability at a point gives the O(eps^2) Taylor bound that step 3 needs.
-/

/-- Gammaℝ is differentiable at 1. -/
theorem differentiableAt_GammaR_one : DifferentiableAt ℂ Complex.Gammaℝ 1 := by
  have hg : DifferentiableAt ℂ Complex.Gamma ((1 : ℂ) / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hcon
    have hre : ((1:ℂ)/2).re = (-(m:ℂ)).re := by rw [hcon]
    rw [Complex.div_re] at hre
    norm_num at hre
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hfun : Complex.Gammaℝ
      = fun s : ℂ => (↑Real.pi) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s
    exact Complex.Gammaℝ_def s
  rw [hfun]
  apply DifferentiableAt.mul
  · apply DifferentiableAt.const_cpow
    · fun_prop
    · left
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact Real.pi_ne_zero
  · exact hg.comp 1 (by fun_prop)

/-- The regularised zeta: zeta(s) - 1/(s-1), defined everywhere (junk at s=1
is irrelevant since we only use it near 1 where it extends). -/
noncomputable def zetaReg (s : ℂ) : ℂ := riemannZeta s - 1 / (s - 1)

/-- zetaReg agrees near s = 1 with an explicitly differentiable function:

    zeta s - 1/(s-1) = [Λ₀(s) - 1/s] / Gammaℝ(s) + (1/(s-1))(1/Gammaℝ(s) - 1)

The first summand is differentiable at 1 (Λ₀ entire, Gammaℝ nonzero there).
The second has a removable singularity since Gammaℝ 1 = 1, so
1/Gammaℝ(s) - 1 vanishes at s = 1 to first order. -/
theorem zetaReg_eq_near_one (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hg : Complex.Gammaℝ s ≠ 0) :
    zetaReg s
      = (completedRiemannZeta₀ s - 1 / s) / Complex.Gammaℝ s
        + (1 / (s - 1)) * (1 / Complex.Gammaℝ s - 1) := by
  unfold zetaReg
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  have hsub : (1 : ℂ) - s = -(s - 1) := by ring
  rw [hsub]
  have hne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  field_simp
  ring

/-- zetaReg is differentiable away from s = 1 (and s = 0). -/
theorem zetaReg_differentiableAt (s : ℂ) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ zetaReg s := by
  unfold zetaReg
  apply DifferentiableAt.sub (differentiableAt_riemannZeta hs1)
  apply DifferentiableAt.div (differentiableAt_const 1)
    (differentiableAt_id.sub (differentiableAt_const 1))
  exact sub_ne_zero_of_ne hs1

/-- The regularised zeta with its removable singularity filled in. -/
noncomputable def zetaRegFull : ℂ → ℂ :=
  Function.update zetaReg 1 ((nhdsWithin (1:ℂ) {(1:ℂ)}ᶜ).limUnder zetaReg)

/-- zetaRegFull agrees with zetaReg away from 1. -/
theorem zetaRegFull_eq_of_ne (s : ℂ) (hs : s ≠ 1) : zetaRegFull s = zetaReg s :=
  Function.update_of_ne hs _ _

/-- zeta s - 1/(s-1) is bounded near s = 1: the pole is simple with residue 1,
so the difference stays finite.  This is what the removable-singularity
theorem needs. -/
theorem zetaReg_bddAbove :
    ∃ r > 0, BddAbove (Norm.norm ∘ zetaReg '' (Metric.ball (1:ℂ) r \ {1})) := by
  -- zetaReg tends to a limit at 1 (the Laurent constant), hence is bounded near 1
  have hlim : ∃ L : ℂ, Filter.Tendsto zetaReg (nhdsWithin 1 {(1:ℂ)}ᶜ) (nhds L) := by
    -- g = 1/Gammaℝ is differentiable at 1 with g 1 = 1
    have hgd : DifferentiableAt ℂ (fun s => 1 / Complex.Gammaℝ s) 1 := by
      apply DifferentiableAt.div (differentiableAt_const 1) differentiableAt_GammaR_one
      rw [Complex.Gammaℝ_one]
      norm_num
    have hg1 : (fun s => 1 / Complex.Gammaℝ s) 1 = 1 := by
      simp [Complex.Gammaℝ_one]
    -- the difference quotient tends to the derivative
    -- A: the manifestly continuous part
    have hAcont : ContinuousAt
        (fun s : ℂ => (completedRiemannZeta₀ s - 1 / s) / Complex.Gammaℝ s) 1 := by
      apply ContinuousAt.div
      · exact (differentiable_completedZeta₀.continuous.continuousAt).sub
          (continuousAt_const.div continuousAt_id one_ne_zero)
      · exact differentiableAt_GammaR_one.continuousAt
      · rw [Complex.Gammaℝ_one]; norm_num
    -- B: the slope of g = 1/Gammaℝ at 1
    have hBlim : Filter.Tendsto
        (fun s : ℂ => (1 / (s - 1)) * (1 / Complex.Gammaℝ s - 1))
        (nhdsWithin 1 {(1:ℂ)}ᶜ) (nhds (deriv (fun s => 1 / Complex.Gammaℝ s) 1)) := by
      have hs := hasDerivAt_iff_tendsto_slope.mp hgd.hasDerivAt
      apply hs.congr'
      filter_upwards [self_mem_nhdsWithin] with s hsne
      rw [slope_def_field, Complex.Gammaℝ_one]
      have hne : s - 1 ≠ 0 := sub_ne_zero_of_ne (by simpa using hsne)
      field_simp
    refine ⟨((completedRiemannZeta₀ 1 - 1 / 1) / Complex.Gammaℝ 1)
      + deriv (fun s => 1 / Complex.Gammaℝ s) 1, ?_⟩
    have hsum := (hAcont.continuousWithinAt.tendsto).add hBlim
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (1:ℂ) (by norm_num : (0:ℝ) < 1/2))]
      with s hsne hsball
    have hs1 : s ≠ 1 := by simpa using hsne
    have hs0 : s ≠ 0 := by
      intro h
      rw [Metric.mem_ball, h, dist_zero_left] at hsball
      simp at hsball
      linarith
    have hgne : Complex.Gammaℝ s ≠ 0 := by
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      rw [Metric.mem_ball, Complex.dist_eq] at hsball
      have := Complex.abs_re_le_norm (s - 1)
      have hre : |(s - 1).re| ≤ ‖s - 1‖ := this
      simp only [Complex.sub_re, Complex.one_re] at hre
      have : |s.re - 1| < 1/2 := lt_of_le_of_lt hre hsball
      cases' abs_lt.mp this with h1 h2
      linarith
    exact (zetaReg_eq_near_one s hs0 hs1 hgne).symm
  obtain ⟨L, hL⟩ := hlim
  have hev : ∀ᶠ s in nhdsWithin (1:ℂ) {(1:ℂ)}ᶜ, ‖zetaReg s‖ ≤ ‖L‖ + 1 := by
    have h1 : ∀ᶠ s in nhdsWithin (1:ℂ) {(1:ℂ)}ᶜ, zetaReg s ∈ Metric.ball L 1 :=
      hL (Metric.ball_mem_nhds L one_pos)
    filter_upwards [h1] with s hsmem
    rw [Metric.mem_ball, dist_eq_norm] at hsmem
    have htri : ‖zetaReg s‖ - ‖L‖ ≤ ‖zetaReg s - L‖ := norm_sub_norm_le _ _
    linarith [le_of_lt hsmem]
  obtain ⟨V, hV, hVsub⟩ := (mem_nhdsWithin_iff_exists_mem_nhds_inter).mp hev
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, hr, ⟨‖L‖ + 1, ?_⟩⟩
  rintro x ⟨s, hs, rfl⟩
  exact hVsub ⟨hrsub hs.1, hs.2⟩

/-- THE KEY LEMMA: zetaRegFull is differentiable at 1.

Differentiable on a punctured ball (zetaReg_differentiableAt) plus bounded
(zetaReg_bddAbove) gives differentiability of the update across the puncture,
by Complex.differentiableOn_update_limUnder_of_bddAbove. -/
theorem zetaRegFull_differentiableAt_one : DifferentiableAt ℂ zetaRegFull 1 := by
  obtain ⟨r, hr, hbdd⟩ := zetaReg_bddAbove
  have hmem : Metric.ball (1:ℂ) r ∈ nhds (1:ℂ) := Metric.ball_mem_nhds 1 hr
  have hdiff : DifferentiableOn ℂ zetaReg (Metric.ball (1:ℂ) r \ {1}) := by
    intro x hx
    exact (zetaReg_differentiableAt x (by simpa using hx.2)).differentiableWithinAt
  have hupd := Complex.differentiableOn_update_limUnder_of_bddAbove hmem hdiff hbdd
  exact (hupd.differentiableAt hmem)

/-- zetaRegFull is analytic at 1: differentiable at 1 and on a punctured
neighbourhood, hence eventually differentiable, hence analytic. -/
theorem zetaRegFull_analyticAt_one : AnalyticAt ℂ zetaRegFull 1 := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  obtain ⟨r, hr, _⟩ := zetaReg_bddAbove
  filter_upwards [Metric.ball_mem_nhds (1:ℂ) hr] with s hsball
  by_cases hs1 : s = 1
  · rw [hs1]; exact zetaRegFull_differentiableAt_one
  · have heq : zetaRegFull =ᶠ[nhds s] zetaReg := by
      filter_upwards [(isOpen_ne (x := (1:ℂ))).mem_nhds hs1] with w hwne
      exact zetaRegFull_eq_of_ne w hwne
    exact (zetaReg_differentiableAt s hs1).congr_of_eventuallyEq heq

/-- From analyticity at 1: zetaRegFull is twice differentiable near 1, so its
first-order Taylor remainder is O(|s-1|^2) on a small ball.

This is the quantitative input step 3 needs -- it is what upgrades the
o(eps) from eps_zeta_second_order to O(eps^2). -/
theorem zetaRegFull_taylor_bound :
    ∃ C > 0, ∃ r > 0, ∀ s : ℂ, ‖s - 1‖ ≤ r →
      ‖zetaRegFull s - zetaRegFull 1 - deriv zetaRegFull 1 * (s - 1)‖
        ≤ C * ‖s - 1‖ ^ 2 := by
  have hps := zetaRegFull_analyticAt_one.hasFPowerSeriesAt
  have hO := hps.isBigO_sub_partialSum_pow 2
  obtain ⟨C, hC, hbw⟩ := hO.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hbw
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hbw
  refine ⟨C, hC, r/2, by linarith, ?_⟩
  intro s hs
  have hy : (s - 1) ∈ Metric.ball (0:ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have := hrsub hy
  simp only [Set.mem_setOf_eq] at this
  have hadd : (1 : ℂ) + (s - 1) = s := by ring
  rw [hadd] at this
  have hnorm : ‖‖s - 1‖ ^ 2‖ = ‖s - 1‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm] at this
  have hpart : (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n zetaRegFull 1 / (Nat.factorial n : ℂ)).partialSum 2 (s - 1)
      = zetaRegFull 1 + deriv zetaRegFull 1 * (s - 1) := by
    rw [FormalMultilinearSeries.partialSum]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [FormalMultilinearSeries.ofScalars, iteratedDeriv_one, iteratedDeriv_zero]
  rw [hpart] at this
  have hre : zetaRegFull s - (zetaRegFull 1 + deriv zetaRegFull 1 * (s - 1))
      = zetaRegFull s - zetaRegFull 1 - deriv zetaRegFull 1 * (s - 1) := by ring
  rw [hre] at this
  exact this

/-- eps * zeta(1+eps) - 1 = eps * zetaRegFull(1+eps) for real eps > 0,
since zetaRegFull(1+eps) = zeta(1+eps) - 1/eps there. -/
theorem eps_zeta_eq_eps_zetaRegFull (eps : ℝ) (heps : 0 < eps) :
    (eps : ℂ) * riemannZeta (1 + (eps : ℂ)) - 1
      = (eps : ℂ) * zetaRegFull (1 + (eps : ℂ)) := by
  have hne : (1 + (eps : ℂ)) ≠ 1 := by
    intro h
    have : (eps : ℂ) = 0 := by linear_combination h
    have : eps = 0 := by exact_mod_cast this
    linarith
  rw [zetaRegFull_eq_of_ne _ hne]
  unfold zetaReg
  have hsub : (1 + (eps : ℂ)) - 1 = (eps : ℂ) := by ring
  rw [hsub]
  have hepsne : (eps : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  field_simp

/-- For real s > 1, the real Dirichlet series equals riemannZeta.
(Extracted from zeta_two_cFac_eq_one's proof, where it was local.) -/
theorem zeta_series_eq (s : ℝ) (hs : 1 < s) :
    ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [one_div, ← Complex.cpow_neg]
  have hb : (0:ℝ) ≤ ((n:ℝ) + 1) := by positivity
  have hoc := Complex.ofReal_cpow hb (-s)
  push_cast at hoc
  push_cast
  exact hoc

/-- zetaRegFull 1 = gamma: the removable-singularity value agrees with the
Laurent constant computed in 6a via the bracket decomposition.

Both are limits of zeta(s) - 1/(s-1) as s -> 1; 6a computes it along the real
axis from above, and zetaRegFull is defined as the limit along the punctured
neighbourhood.  Uniqueness of limits identifies them. -/
theorem zetaRegFull_one_eq_gamma :
    zetaRegFull 1 = ((Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  -- zetaRegFull is continuous at 1 (differentiable there), so it is the limit
  -- of zetaReg along any filter tending to 1 within the punctured plane.
  have hcont : ContinuousAt zetaRegFull 1 :=
    zetaRegFull_differentiableAt_one.continuousAt
  -- along real s decreasing to 1, zetaReg s = (real series) - 1/(s-1) -> gamma by 6a
  have hcast : Filter.Tendsto (fun s : ℝ => ((s : ℂ)))
      (nhdsWithin (1:ℝ) (Set.Ioc 1 2)) (nhds ((1:ℝ) : ℂ)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    exact Complex.continuous_ofReal.tendsto 1
  have hreal : Filter.Tendsto (fun s : ℝ => zetaRegFull ((s : ℂ)))
      (nhdsWithin 1 (Set.Ioc 1 2)) (nhds (zetaRegFull 1)) := by
    have h := hcont.tendsto.comp hcast
    simpa only [Function.comp_def, Complex.ofReal_one] using h
  have hgamma : Filter.Tendsto (fun s : ℝ => zetaRegFull ((s : ℂ)))
      (nhdsWithin 1 (Set.Ioc 1 2)) (nhds ((Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    have h6a := zeta_laurent_constant
    have hcomp : Filter.Tendsto
        (fun s : ℝ => (((∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1) : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioc 1 2)) (nhds ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp h6a
    apply hcomp.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1:ℝ) < s := hs.1
    have hne : ((s : ℂ)) ≠ 1 := by
      intro hcon
      have : (s : ℝ) = 1 := by exact_mod_cast hcon
      linarith
    rw [zetaRegFull_eq_of_ne _ hne]
    unfold zetaReg
    rw [← zeta_series_eq s hs1]
    push_cast
    have hsne : (s : ℂ) - 1 ≠ 0 := sub_ne_zero_of_ne hne
    field_simp
  have hnb : (nhdsWithin (1:ℝ) (Set.Ioc 1 2)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioc (by norm_num : (1:ℝ) ≠ 2)]
    exact ⟨le_refl 1, by norm_num⟩
  exact tendsto_nhds_unique hreal hgamma

/-- The uniform second-order bound, as an existence statement.  The constant C
and the range eps0 are what the certified computation supplies; here they are
existentially quantified, which is all step 3 needs. -/
theorem eps_zeta_uniform :
    ∃ C > 0, ∃ eps0 > 0, eps0 ≤ 1 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
      |eps * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))) - 1
        - Real.eulerMascheroniConstant * eps| ≤ C * eps ^ 2 := by
  obtain ⟨C, hC, r, hr, hbound⟩ := zetaRegFull_taylor_bound
  refine ⟨C + ‖deriv zetaRegFull 1‖, by positivity, min r 1, by positivity,
    min_le_right _ _, ?_⟩
  intro eps heps hle
  have hle_r : eps ≤ r := le_trans hle (min_le_left _ _)
  have hne : ((1 : ℂ) + (eps : ℂ)) - 1 = (eps : ℂ) := by ring
  have hnorm : ‖((1 : ℂ) + (eps : ℂ)) - 1‖ = eps := by
    rw [hne, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
  have htay := hbound ((1 : ℂ) + (eps : ℂ)) (by rw [hnorm]; exact hle_r)
  rw [hnorm, hne, zetaRegFull_one_eq_gamma] at htay
  -- eps * zeta(1+eps) - 1 = eps * zetaRegFull(1+eps)
  have hkey := eps_zeta_eq_eps_zetaRegFull eps heps
  -- transport to the real series
  have hser : riemannZeta (1 + (eps : ℂ))
      = ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps)) : ℝ) : ℂ) := by
    rw [zeta_series_eq (1 + eps) (by linarith)]
    push_cast
    ring_nf
  have hle1 : eps ≤ 1 := le_trans hle (min_le_right _ _)
  have hC_eq : ((eps * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))) - 1
      - Real.eulerMascheroniConstant * eps : ℝ) : ℂ)
      = (eps : ℂ) * (zetaRegFull (1 + (eps:ℂ))
          - ((Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul,
      ← hser]
    push_cast
    linear_combination hkey
  have habs : |eps * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(1+eps))) - 1
      - Real.eulerMascheroniConstant * eps|
      = ‖(eps : ℂ) * (zetaRegFull (1 + (eps:ℂ))
          - ((Real.eulerMascheroniConstant : ℝ) : ℂ))‖ := by
    rw [← hC_eq, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
  have hsplit : zetaRegFull (1 + (eps:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
      = (zetaRegFull (1 + (eps:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
          - deriv zetaRegFull 1 * (eps:ℂ)) + deriv zetaRegFull 1 * (eps:ℂ) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (zetaRegFull (1 + (eps:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
      - deriv zetaRegFull 1 * (eps:ℂ)) (deriv zetaRegFull 1 * (eps:ℂ))
  have hd : ‖deriv zetaRegFull 1 * (eps:ℂ)‖ = ‖deriv zetaRegFull 1‖ * eps := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
  rw [hd] at htri
  have hstep : eps * ‖zetaRegFull (1 + (eps:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
      - deriv zetaRegFull 1 * (eps:ℂ) + deriv zetaRegFull 1 * (eps:ℂ)‖
      ≤ eps * (C * eps ^ 2 + ‖deriv zetaRegFull 1‖ * eps) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt heps)
    linarith [htri, htay]
  have hfin : eps * (C * eps ^ 2 + ‖deriv zetaRegFull 1‖ * eps)
      ≤ (C + ‖deriv zetaRegFull 1‖) * eps ^ 2 := by
    have h1 : eps * (C * eps ^ 2) ≤ C * eps ^ 2 := by
      have hpos : (0:ℝ) ≤ C * eps ^ 2 := by positivity
      nlinarith [hpos, hle1, heps]
    have h2 : eps * (‖deriv zetaRegFull 1‖ * eps) = ‖deriv zetaRegFull 1‖ * eps ^ 2 := by ring
    nlinarith [h1, h2]
  linarith [hstep, hfin]

/-- The s-uniformity input for step 3.

Mirrors `NumericalFacts.beta` in the main development, where the sup of
|d_s g_i(s)| over s in (1,2), uniform in i, is a certified input rather than a
derived bound.  Supplied here by odd-proof/numerics/mr_certified.py, whose interval
sweep ranges over s in [1,2] as well as the z-circle. -/
structure OddCoeffFacts (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) : Prop where
  nonneg : ∀ j : ℕ, 0 ≤ betaFam j
  /-- The per-j bounds are summable against 2^j.  This is what the
  coefficient-sum identity of step 4 needs, and it is the analogue of the
  main development's beta_i sweep rather than of its uniform bound. -/
  fam_summable : Summable (fun j : ℕ => betaFam j * (2:ℝ) ^ j)
  deriv_exists : ∀ j : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
    HasDerivAt (fun t : ℝ => hCoeff t j) (deriv (fun t : ℝ => hCoeff t j) x) x
  deriv_bound : ∀ j : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
    ‖deriv (fun t : ℝ => hCoeff t j) x‖ ≤ betaFam j
  /-- The coefficients converge to their s = 1 values from the right.

  Certified alongside the derivative bound by the same interval sweep; the
  main development's `gManu_tendsto_cCoeff` is the analogue. -/
  tendsto_one : ∀ j : ℕ, Filter.Tendsto (fun t : ℝ => hCoeff t j)
    (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (hCoeff 1 j))
  /-- The first-order coefficients b_j = d_s h_j(1) are the limits from the
  right.  The analogue of `bHat` in the main development. -/
  tendsto_deriv : ∀ j : ℕ, Filter.Tendsto (fun t : ℝ => deriv (fun x : ℝ => hCoeff x j) t)
    (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (bHatOdd j))
  /-- The second derivative exists and is bounded, uniformly in j.
  The analogue of `gammahat` in the main development, certified by the same
  interval sweep. -/
  deriv2_exists : ∀ j : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
    HasDerivAt (fun t : ℝ => deriv (fun x : ℝ => hCoeff x j) t)
      (deriv (fun t : ℝ => deriv (fun x : ℝ => hCoeff x j) t) x) x
  deriv2_bound : ∀ j : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
    ‖deriv (fun t : ℝ => deriv (fun x : ℝ => hCoeff x j) t) x‖ ≤ betaFam j

/-- The mean-value step: |h_j(s) - h_j(t)| <= betaS |s - t| on (1,2),
uniformly in j.  Transferred from gManu_lipschitz_interior. -/
theorem hCoeff_lipschitz (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd) (j : ℕ)
    (t s : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 2) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    ‖hCoeff s j - hCoeff t j‖ ≤ betaFam j * ‖s - t‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun x : ℝ => deriv (fun u : ℝ => hCoeff u j) x)
    (fun x hx => (hf.deriv_exists j x hx).hasDerivWithinAt)
    (fun x hx => hf.deriv_bound j x hx) (convex_Ioo 1 2) ht hs

/-! ### 6c step 3: the assembly

    fOdd k = int_{Ioi 1} FkOdd k s ds                        [item 1]
           = int_{Ioo 1 2} + int_{Ici 2}                      [item 5]
           = int_{Ioi 0} FkOdd k (1+e^-u) e^-u du + tail      [item 5]

Insert FkOdd_expansion' and replace, term by term:
  * u_*(u) = log zeta(1+e^-u) by u, error controlled by eps_zeta_uniform
  * h_j(1+e^-u) by h_j(1), error controlled by hCoeff_lipschitz

The sum over j <= k is FINITE, so it commutes with the integral.  The leading
term is sum_j h_j(1) * int u^(k-j) e^-u/(k-j)! = sum_j h_j(1) = H(1,1) = 1/2
(gamma_normalised, hCoeff_sum_one); the next order gives beta 2^-k via
gamma_normalised_two and hCoeff_sum_two; the rest is bounded by
gamma_normalised_three.
-/

/-- The leading order: replacing u_* by u and h_j(1+e^-u) by h_j(1) gives
sum_j h_j(1), which is H(1,1) = 1/2. -/
theorem fOdd_leading_order (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1),
      (hCoeff 1 j).re * (∫ u in Set.Ioi (0:ℝ), u ^ (k - j) * Real.exp (-u))
        / (Nat.factorial (k - j))
      = ∑ j ∈ Finset.range (k + 1), (hCoeff 1 j).re := by
  apply Finset.sum_congr rfl
  intro j _
  have hg : (∫ u in Set.Ioi (0:ℝ), u ^ (k - j) * Real.exp (-u))
      = (Nat.factorial (k - j) : ℝ) := by
    have h := integral_exp_neg_mul_pow (k - j)
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  rw [hg]
  field_simp

/-! ### The correct substitution for step 3: u = log zeta(s)

`substitution_near_pole` (item 5) uses s = 1 + e^-u, which is convenient but
wrong for the expansion: FkOdd's expansion is in powers of u(s) = log zeta(s),
and 1 + e^-u does not make u(s) equal u.

Substituting u = log zeta(s) instead makes u the integration variable, so the
u^{k-j} factor is exact and the whole approximation moves into the Jacobian
-s'(u), where eps_zeta_uniform controls it.

zeta is strictly decreasing on (1, inf) from +inf to 1, so u = log zeta maps
(1, inf) onto (0, inf) monotonically -- a valid change of variable. -/

/-- zeta restricted to reals > 1, as the real series. -/
noncomputable def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)

/-- u(s) = log zeta(s) is strictly decreasing on (1, inf). -/
theorem uOf_strictAnti : StrictAntiOn uOf (Set.Ioi 1) := by
  intro a ha b hb hab
  have ha1 : (1:ℝ) < a := ha
  have hb1 : (1:ℝ) < b := hb
  -- zeta is strictly decreasing: each term (n+1)^-s is, for n >= 1
  have hsummable : ∀ t : ℝ, 1 < t → Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-t)) := by
    intro t ht
    have hb := Real.summable_nat_rpow.mpr (by linarith : (-t:ℝ) < -1)
    apply ((summable_nat_add_iff 1).mpr hb).congr
    intro n
    push_cast
    ring_nf
  have hzlt : (∑' n : ℕ, ((n:ℝ) + 1) ^ (-b)) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-a) := by
    have hle : (fun n : ℕ => ((n:ℝ) + 1) ^ (-b)) ≤ fun n : ℕ => ((n:ℝ) + 1) ^ (-a) := by
      intro n
      apply Real.rpow_le_rpow_of_exponent_le (by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith) (by linarith)
    have hstrict : ((1:ℕ):ℝ) + 1 ≤ ((1:ℕ):ℝ) + 1 := le_refl _
    apply Summable.tsum_lt_tsum (i := 1) hle _ (hsummable b hb1) (hsummable a ha1)
    show (((1:ℕ):ℝ) + 1) ^ (-b) < (((1:ℕ):ℝ) + 1) ^ (-a)
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hpos : ∀ t : ℝ, 1 < t → (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-t) := by
    intro t ht
    have hle := (hsummable t ht).le_tsum 0 (fun n _ => by positivity)
    calc (0:ℝ) < ((0:ℝ) + 1) ^ (-t) := by norm_num
      _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-t) := by simpa using hle
  have hza := hpos a ha1
  have hzb := hpos b hb1
  unfold uOf
  exact Real.log_lt_log hzb hzlt

/-- u maps (1, inf) onto (0, inf). -/
theorem uOf_image : uOf '' (Set.Ioi 1) = Set.Ioi 0 := by
  -- u = log zeta, zeta > 1 on (1,inf) so u > 0; zeta -> inf at 1+ and -> 1 at inf
  have hsummable : ∀ t : ℝ, 1 < t → Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-t)) := by
    intro t ht
    have hb := Real.summable_nat_rpow.mpr (by linarith : (-t:ℝ) < -1)
    apply ((summable_nat_add_iff 1).mpr hb).congr
    intro n
    push_cast
    ring_nf
  have hzgt : ∀ s : ℝ, 1 < s → 1 < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
    intro t ht
    -- the n = 0 term is 1 and the n = 1 term is positive
    have hsum2 : ((0:ℝ) + 1) ^ (-t) + ((1:ℝ) + 1) ^ (-t)
        ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-t) := by
      have hfin := (hsummable t ht).sum_le_tsum (Finset.range 2)
        (fun n _ => by positivity)
      rw [Finset.sum_range_succ, Finset.sum_range_one] at hfin
      push_cast at hfin
      exact hfin
    have h0 : ((0:ℝ) + 1) ^ (-t) = 1 := by norm_num
    have h1 : (0:ℝ) < ((1:ℝ) + 1) ^ (-t) := by positivity
    linarith
  have htop : Filter.Tendsto uOf (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
    -- zeta(s) - 1/(s-1) -> gamma (6a), and 1/(s-1) -> inf, so zeta -> inf
    have hpole : Filter.Tendsto (fun s : ℝ => 1 / (s - 1))
        (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
      simp only [one_div]
      apply Filter.Tendsto.comp tendsto_inv_nhdsGT_zero
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Filter.Tendsto (fun s : ℝ => s - 1) (nhds 1) (nhds ((1:ℝ) - 1)) :=
          ((continuous_id.sub continuous_const).tendsto 1)
        rw [sub_self] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs1 : (1:ℝ) < s := hs
        simp only [Set.mem_Ioi]
        linarith
    have hz : Filter.Tendsto (fun s : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))
        (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
      -- zeta(s) >= 1/(s-1) by comparison with the integral (tsum_integral_Ioc_eq)
      have hge : ∀ s : ℝ, 1 < s → 1 / (s - 1) ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
        intro t ht
        rw [← tsum_integral_Ioc_eq t ht]
        apply Summable.tsum_le_tsum
        · intro n
          have hb := zetaBracket_nonneg_of_mem n t ht
          unfold zetaBracket at hb
          linarith
        · apply Summable.of_nonneg_of_le _ _ (hsummable t ht)
          · intro n
            apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
            intro x hx
            have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
            exact Real.rpow_nonneg (by linarith [hx.1]) _
          · intro n
            have hb := zetaBracket_nonneg_of_mem n t ht
            unfold zetaBracket at hb
            linarith
        · exact hsummable t ht
      apply Filter.tendsto_atTop_mono' _ _ hpole
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hge s hs
    unfold uOf
    exact Real.tendsto_log_atTop.comp hz
  have hbot : Filter.Tendsto uOf Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    -- zeta(s) -> 1 as s -> inf (the n=0 term is 1, the rest tends to 0)
    have hz1 : Filter.Tendsto (fun s : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))
        Filter.atTop (nhds 1) := by
      have hlim : ∀ n : ℕ, Filter.Tendsto (fun s : ℝ => ((n:ℝ) + 1) ^ (-s))
          Filter.atTop (nhds (if n = 0 then 1 else 0)) := by
        intro n
        by_cases hn : n = 0
        · subst hn
          simp only [if_pos rfl]
          have hone : ∀ s : ℝ, (((0:ℕ):ℝ) + 1) ^ (-s) = 1 := by
            intro s
            norm_num
          simp only [hone]
          exact tendsto_const_nhds
        · simp only [if_neg hn]
          have hb : (1:ℝ) < (n:ℝ) + 1 := by
            have : (1:ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
            have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast this
            linarith
          have hneg : Filter.Tendsto (fun s : ℝ => -s) Filter.atTop Filter.atBot :=
            Filter.tendsto_neg_atTop_atBot
          exact (tendsto_rpow_atBot_of_base_gt_one _ hb).comp hneg
      have hdom : ∀ᶠ s : ℝ in Filter.atTop, ∀ n : ℕ,
          ‖((n:ℝ) + 1) ^ (-s)‖ ≤ ((n:ℝ) + 1) ^ (-(2:ℝ)) := by
        filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with s hs n
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply Real.rpow_le_rpow_of_exponent_le (by
          have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith) (by linarith)
      have hb2 : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-(2:ℝ))) := hsummable 2 (by norm_num)
      have := tendsto_tsum_of_dominated_convergence hb2 hlim hdom
      simpa using this
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · unfold uOf
      have := Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)
      have hcomp := this.tendsto.comp hz1
      rw [Real.log_one] at hcomp
      exact hcomp
    · filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with s hs
      simp only [Set.mem_Ioi]
      unfold uOf
      exact Real.log_pos (hzgt s hs)
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    simp only [Set.mem_Ioi]
    unfold uOf
    exact Real.log_pos (hzgt s hs)
  · intro hy
    simp only [Set.mem_Ioi] at hy
    -- continuity of uOf on (1, inf)
    have hzcont : ContinuousOn (fun s : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))
        (Set.Ioi 1) := by
      apply ContinuousOn.mono _ (Set.Subset.refl _)
      intro s0 hs0
      have hs01 : (1:ℝ) < s0 := hs0
      set d := (s0 - 1) / 2 with hd
      have hdpos : 0 < d := by rw [hd]; linarith
      -- on [1+d, inf) the series converges uniformly, dominated by (n+1)^-(1+d)
      have hdom : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-(1 + d))) :=
        hsummable (1 + d) (by linarith)
      have hunif : ∀ n : ℕ, ∀ s ∈ Set.Ici (1 + d),
          ‖((n:ℝ) + 1) ^ (-s)‖ ≤ ((n:ℝ) + 1) ^ (-(1 + d)) := by
        intro n s hs
        have hsle : 1 + d ≤ s := hs
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply Real.rpow_le_rpow_of_exponent_le (by
          have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith) (by linarith)
      have hOn : ContinuousOn (fun s : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))
          (Set.Ici (1 + d)) := by
        apply continuousOn_tsum _ hdom hunif
        intro n
        have hb : ((n:ℝ) + 1) ≠ 0 := by positivity
        apply Continuous.continuousOn
        exact (Real.continuous_const_rpow hb).comp continuous_neg
      apply (hOn.continuousAt _).continuousWithinAt
      apply Ici_mem_nhds
      rw [hd]
      linarith
    have hcont : ContinuousOn uOf (Set.Ioi 1) := by
      unfold uOf
      apply ContinuousOn.log hzcont
      intro s hs
      have := hzgt s hs
      linarith
    -- pick a < b in (1,inf) with uOf b < y < uOf a, then IVT
    obtain ⟨a, ha1, hay⟩ : ∃ a : ℝ, 1 < a ∧ y < uOf a := by
      have := htop.eventually (Filter.eventually_gt_atTop y)
      obtain ⟨V, hV, hVsub⟩ := (mem_nhdsWithin_iff_exists_mem_nhds_inter).mp this
      obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hV
      refine ⟨1 + r/2, by linarith, ?_⟩
      apply hVsub
      constructor
      · apply hrsub
        rw [Metric.mem_ball, Real.dist_eq]
        rw [show (1 + r/2 - 1 : ℝ) = r/2 by ring, abs_of_pos (by linarith)]
        linarith
      · simp only [Set.mem_Ioi]; linarith
    obtain ⟨b, hba, hby⟩ : ∃ b : ℝ, a < b ∧ uOf b < y := by
      have := hbot.eventually (eventually_nhdsWithin_of_eventually_nhds
        (eventually_lt_nhds hy))
      obtain ⟨b, hb⟩ := (this.and (Filter.eventually_gt_atTop a)).exists
      exact ⟨b, hb.2, hb.1⟩
    have hsub : Set.Icc a b ⊆ Set.Ioi 1 := by
      intro x hx
      simp only [Set.mem_Ioi]
      linarith [hx.1]
    have hivt := intermediate_value_Icc' (le_of_lt hba) (hcont.mono hsub)
    have hmem : y ∈ Set.Icc (uOf b) (uOf a) := ⟨le_of_lt hby, le_of_lt hay⟩
    obtain ⟨x, hx, hxy⟩ := hivt hmem
    exact ⟨x, hsub hx, hxy⟩

/-- log(n+1) (n+1)^-s is summable for s > 1: compare with (n+1)^-s' for
1 < s' < s, using log(n+1) <= C (n+1)^(s-s') for large n. -/
theorem log_rpow_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-s)) := by
  set s' := (1 + s) / 2 with hs'
  have hs'1 : 1 < s' := by rw [hs']; linarith
  have hs's : s' < s := by rw [hs']; linarith
  have hbase : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s')) := by
    have hb := Real.summable_nat_rpow.mpr (by linarith : (-s':ℝ) < -1)
    apply ((summable_nat_add_iff 1).mpr hb).congr
    intro n
    push_cast
    ring_nf
  -- log(n+1) (n+1)^-s = [log(n+1) (n+1)^-(s-s')] (n+1)^-s', and the bracket -> 0
  have hbdd : ∃ C > 0, ∀ n : ℕ,
      Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-(s - s')) ≤ C := by
    -- log x <= x^a / a for x >= 1, a > 0, so log x * x^-a <= 1/a
    refine ⟨1 / (s - s'), by positivity, ?_⟩
    intro n
    have hx1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hxpos : (0:ℝ) < (n:ℝ) + 1 := by linarith
    have ha : (0:ℝ) < s - s' := by linarith
    have hlog : Real.log ((n:ℝ) + 1) ≤ ((n:ℝ) + 1) ^ (s - s') / (s - s') := by
      -- a log x <= x^a - 1 <= x^a, from log t <= t - 1 with t = x^a
      have hxa : (0:ℝ) < ((n:ℝ) + 1) ^ (s - s') := by positivity
      have hlt := Real.log_le_sub_one_of_pos hxa
      rw [Real.log_rpow hxpos] at hlt
      rw [le_div_iff₀ ha]
      calc Real.log ((n:ℝ) + 1) * (s - s')
          = (s - s') * Real.log ((n:ℝ) + 1) := by ring
        _ ≤ ((n:ℝ) + 1) ^ (s - s') - 1 := hlt
        _ ≤ ((n:ℝ) + 1) ^ (s - s') := by linarith
    calc Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-(s - s'))
        ≤ (((n:ℝ) + 1) ^ (s - s') / (s - s')) * ((n:ℝ) + 1) ^ (-(s - s')) := by
          apply mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = 1 / (s - s') := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hxpos]
          simp
  obtain ⟨C, hC, hCb⟩ := hbdd
  apply Summable.of_nonneg_of_le _ _ (hbase.mul_left C)
  · intro n
    have hlog : (0:ℝ) ≤ Real.log ((n:ℝ) + 1) := by
      apply Real.log_nonneg
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hpow : (0:ℝ) ≤ ((n:ℝ) + 1) ^ (-s) := by positivity
    exact mul_nonneg hlog hpow
  · intro n
    have hfac : Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-s)
        = (Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-(s - s'))) * ((n:ℝ) + 1) ^ (-s') := by
      rw [mul_assoc, ← Real.rpow_add (by positivity)]
      ring_nf
    rw [hfac]
    apply mul_le_mul_of_nonneg_right (hCb n) (by positivity)

/-- The zeta series is summable for s > 1. -/
theorem zetaR_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s)) := by
  have hb := Real.summable_nat_rpow.mpr (by linarith : (-s:ℝ) < -1)
  apply ((summable_nat_add_iff 1).mpr hb).congr
  intro n
  push_cast
  ring_nf

/-- The zeta series is positive for s > 1. -/
theorem zetaR_pos (s : ℝ) (hs : 1 < s) :
    (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
  have hle := (zetaR_summable s hs).le_tsum 0 (fun n _ => by positivity)
  calc (0:ℝ) < ((0:ℝ) + 1) ^ (-s) := by norm_num
    _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by simpa using hle

/-- zeta(s) > 1 for s > 1: the n = 0 term is 1 and the rest are positive. -/
theorem zetaR_gt_one (s : ℝ) (hs : 1 < s) :
    1 < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
  have hsum2 : ((0:ℝ) + 1) ^ (-s) + ((1:ℝ) + 1) ^ (-s)
      ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
    have hfin := (zetaR_summable s hs).sum_le_tsum (Finset.range 2)
      (fun n _ => by positivity)
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hfin
    push_cast at hfin
    exact hfin
  have h0 : ((0:ℝ) + 1) ^ (-s) = 1 := by norm_num
  have h1 : (0:ℝ) < ((1:ℝ) + 1) ^ (-s) := by positivity
  linarith


/-- The termwise derivative of the zeta series. -/
noncomputable def zetaRderiv (s : ℝ) : ℝ :=
  ∑' n : ℕ, (-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-s)

/-- The zeta series is differentiable on (1, inf) with the termwise derivative.

Via hasDerivAt_of_tendstoLocallyUniformlyOn: the partial sums converge
pointwise, their derivatives converge locally uniformly (dominated by
log(n+1)(n+1)^(-(1+d)) on [1+d, inf)), and Ioi 1 is open. -/
theorem zetaR_hasDerivAt (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-t)) (zetaRderiv s) s := by
  have hsummable : ∀ t : ℝ, 1 < t → Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-t)) := by
    intro t ht
    have hb := Real.summable_nat_rpow.mpr (by linarith : (-t:ℝ) < -1)
    apply ((summable_nat_add_iff 1).mpr hb).congr
    intro n
    push_cast
    ring_nf
  -- each term's derivative
  have hterm : ∀ (n : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (fun x : ℝ => ((n:ℝ) + 1) ^ (-x))
        ((-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-t)) t := by
    intro n t _
    have hb : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have h := HasDerivAt.const_rpow hb (hasDerivAt_neg t)
    simpa [mul_comm, mul_assoc] using h
  apply hasDerivAt_of_tendstoLocallyUniformlyOn (s := Set.Ioi 1)
    (l := Filter.atTop) isOpen_Ioi
    (f := fun N : Finset ℕ => fun t : ℝ => ∑ n ∈ N, ((n:ℝ) + 1) ^ (-t))
    (f' := fun N : Finset ℕ => fun t : ℝ =>
      ∑ n ∈ N, (-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-t))
  · -- local uniform convergence of the differentiated series
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi]
    intro K hKsub hKcomp
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · subst hKe
      simp [tendstoUniformlyOn_empty]
    · obtain ⟨c, hcK, hcmin⟩ := hKcomp.exists_isMinOn hKne continuousOn_id
      have hc1 : (1:ℝ) < c := hKsub hcK
      apply tendstoUniformlyOn_tsum
        (u := fun n : ℕ => Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-c))
        (log_rpow_summable c hc1)
      intro n x hx
      have hxc : c ≤ x := hcmin hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlog : |(-Real.log ((n:ℝ) + 1))| = Real.log ((n:ℝ) + 1) := by
        rw [abs_neg, abs_of_nonneg]
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      have hpow : |((n:ℝ) + 1) ^ (-x)| = ((n:ℝ) + 1) ^ (-x) :=
        abs_of_nonneg (by positivity)
      rw [hlog, hpow]
      apply mul_le_mul_of_nonneg_left _ (by
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith)
      apply Real.rpow_le_rpow_of_exponent_le (by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith) (by linarith)
  · -- each partial sum has the stated derivative
    filter_upwards with N t ht
    have ht0 : (0:ℝ) < t := by
      have : (1:ℝ) < t := ht
      linarith
    have h := HasDerivAt.sum (u := N) (A := fun n => fun x : ℝ => ((n:ℝ) + 1) ^ (-x))
      (A' := fun n => (-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-t))
      (fun n _ => hterm n t ht0)
    have hfun : (fun t : ℝ => ∑ n ∈ N, ((n:ℝ) + 1) ^ (-t))
        = ∑ i ∈ N, (fun x : ℝ => ((i:ℝ) + 1) ^ (-x)) := by
      funext x
      rw [Finset.sum_apply]
    rw [hfun]
    simpa using h
  · -- pointwise convergence of the partial sums
    intro t ht
    have ht1 : (1:ℝ) < t := ht
    exact (hsummable t ht1).hasSum
  · exact hs

/-- u = log zeta has derivative zeta'/zeta on (1, inf). -/
theorem uOf_hasDerivAt (s : ℝ) (hs : 1 < s) :
    HasDerivAt uOf (zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))) s := by
  have hz := zetaR_hasDerivAt s hs
  have hzpos : (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
    have hsummable : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s)) := by
      have hb := Real.summable_nat_rpow.mpr (by linarith : (-s:ℝ) < -1)
      apply ((summable_nat_add_iff 1).mpr hb).congr
      intro n
      push_cast
      ring_nf
    have hle := hsummable.le_tsum 0 (fun n _ => by positivity)
    calc (0:ℝ) < ((0:ℝ) + 1) ^ (-s) := by norm_num
      _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by simpa using hle
  unfold uOf
  exact hz.log (ne_of_gt hzpos)

/-- The change of variables u = log zeta(s), stated without needing the
inverse function: for g integrable on (0, inf),

    int_{Ioi 0} g u du = int_{Ioi 1} |u'(s)| g(u(s)) ds.

Applying this with g(u) = [the expansion at u] turns the s-integral into a
u-integral where the u^{k-j} factors are exact powers of the variable. -/
theorem uOf_change_of_variables (g : ℝ → ℝ) :
    (∫ u in Set.Ioi (0:ℝ), g u)
      = ∫ s in Set.Ioi (1:ℝ),
          |zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))| * g (uOf s) := by
  rw [← uOf_image]
  apply MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
  · intro s hs
    exact (uOf_hasDerivAt s hs).hasDerivWithinAt
  · exact uOf_strictAnti.injOn

/-- The real derivative identification: for real s > 1,

    zetaRderiv s + 1/(s-1)^2 = (deriv zetaRegFull s).re

Extracted from zetaRderiv_pole_bound, where it was local. -/
theorem zetaRderiv_eq_re (s : ℝ) (hs1 : 1 < s) :
    zetaRderiv s + 1 / (s - 1) ^ 2 = (deriv zetaRegFull ((s:ℂ))).re := by
  have hne : ((s:ℂ)) ≠ 1 := by
    intro hc
    have : (s:ℝ) = 1 := by exact_mod_cast hc
    linarith
  have hdiff : DifferentiableAt ℂ zetaRegFull ((s:ℂ)) := by
    have h := zetaReg_differentiableAt ((s:ℂ)) hne
    apply h.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne (x := (1:ℂ))).mem_nhds hne] with w hw
    exact zetaRegFull_eq_of_ne w hw
  have hreal := hdiff.hasDerivAt.real_of_complex
  have hrestrict : ∀ x : ℝ, 1 < x →
      (zetaRegFull ((x:ℂ))).re = (∑' n : ℕ, ((n:ℝ) + 1) ^ (-x)) - 1 / (x - 1) := by
    intro x hx
    have hnex : ((x:ℂ)) ≠ 1 := by
      intro hc
      have : (x:ℝ) = 1 := by exact_mod_cast hc
      linarith
    rw [zetaRegFull_eq_of_ne _ hnex]
    unfold zetaReg
    rw [← zeta_series_eq x hx]
    have hsub : ((x:ℂ)) - 1 = (((x - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub]
    exact Complex.ofReal_re _
  have hpole : HasDerivAt (fun x : ℝ => 1 / (x - 1)) (-(1 / (s - 1) ^ 2)) s := by
    have hnz : s - 1 ≠ 0 := by intro h; linarith
    have h := ((hasDerivAt_id s).sub_const 1).inv (by simpa using hnz)
    simp only [id_eq] at h
    have hf : (fun x : ℝ => x - 1)⁻¹ = fun x : ℝ => 1 / (x - 1) := by
      funext x
      simp [one_div]
    rw [hf] at h
    have harith : -(1 / (s - 1) ^ 2) = -1 / (s - 1) ^ 2 := by ring
    rw [harith]
    exact h
  have hdirect : HasDerivAt (fun x : ℝ => (∑' n : ℕ, ((n:ℝ) + 1) ^ (-x)) - 1 / (x - 1))
      (zetaRderiv s + 1 / (s - 1) ^ 2) s := by
    have h := (zetaR_hasDerivAt s hs1).sub hpole
    have hf : ((fun t : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-t)) - fun x : ℝ => 1 / (x - 1))
        = fun x : ℝ => (∑' n : ℕ, ((n:ℝ) + 1) ^ (-x)) - 1 / (x - 1) := by
      funext x
      rfl
    rw [hf] at h
    have harith2 : zetaRderiv s + 1 / (s - 1) ^ 2
        = zetaRderiv s - -(1 / (s - 1) ^ 2) := by ring
    rw [harith2]
    exact h
  have hcongr : HasDerivAt (fun x : ℝ => (zetaRegFull ((x:ℂ))).re)
      (zetaRderiv s + 1 / (s - 1) ^ 2) s := by
    apply hdirect.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hs1] with x hx
    exact hrestrict x hx
  exact hcongr.unique hreal


/-- zeta'(s) + 1/(s-1)^2 is bounded near s = 1.

This is the derivative of the Laurent expansion: zetaRegFull = zeta - 1/(s-1)
is analytic at 1 (zetaRegFull_analyticAt_one), so its derivative is bounded on
a neighbourhood, and d/ds[1/(s-1)] = -1/(s-1)^2. -/
theorem zetaRderiv_pole_bound :
    ∃ C > 0, ∃ r > 0, ∀ s : ℝ, 1 < s → s - 1 ≤ r →
      |zetaRderiv s + 1 / (s - 1) ^ 2| ≤ C := by
  -- zetaRegFull is analytic at 1, so deriv zetaRegFull is bounded near 1
  have hana := zetaRegFull_analyticAt_one
  obtain ⟨r0, hr0, hcont⟩ : ∃ r > 0, ∀ z ∈ Metric.ball (1:ℂ) r,
      ‖deriv zetaRegFull z‖ ≤ ‖deriv zetaRegFull 1‖ + 1 := by
    -- deriv of an analytic function is continuous at the point
    have hd : ContinuousAt (deriv zetaRegFull) 1 := by
      have := hana.deriv
      exact this.continuousAt
    have hnb : ContinuousAt (fun z => ‖deriv zetaRegFull z‖) 1 := hd.norm
    have hev := hnb (Metric.ball_mem_nhds (‖deriv zetaRegFull 1‖) one_pos)
    rw [Filter.mem_map, Metric.mem_nhds_iff] at hev
    obtain ⟨r, hr, hrsub⟩ := hev
    refine ⟨r, hr, ?_⟩
    intro z hz
    have := hrsub hz
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at this
    have habs := abs_lt.mp this
    linarith [habs.2]
  refine ⟨‖deriv zetaRegFull 1‖ + 1, by positivity, r0 / 2, by linarith, ?_⟩
  intro s hs1 hsr
  have hsball : ((s : ℂ)) ∈ Metric.ball (1:ℂ) r0 := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have : ((s:ℂ)) - 1 = ((s - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  -- zetaRegFull is differentiable at s (complex), restrict to the reals
  have hdiff : DifferentiableAt ℂ zetaRegFull ((s:ℂ)) := by
    have hne : ((s:ℂ)) ≠ 1 := by
      intro hc
      have : (s:ℝ) = 1 := by exact_mod_cast hc
      linarith
    have := zetaReg_differentiableAt ((s:ℂ)) hne
    apply this.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne (x := (1:ℂ))).mem_nhds hne] with w hw
    exact zetaRegFull_eq_of_ne w hw
  have hreal := hdiff.hasDerivAt.real_of_complex
  -- the real restriction equals zetaR - 1/(s-1)
  have hrestrict : ∀ x : ℝ, 1 < x →
      (zetaRegFull ((x:ℂ))).re = (∑' n : ℕ, ((n:ℝ) + 1) ^ (-x)) - 1 / (x - 1) := by
    intro x hx
    have hne : ((x:ℂ)) ≠ 1 := by
      intro hc
      have : (x:ℝ) = 1 := by exact_mod_cast hc
      linarith
    rw [zetaRegFull_eq_of_ne _ hne]
    unfold zetaReg
    rw [← zeta_series_eq x hx]
    have hsub : ((x:ℂ)) - 1 = (((x - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub]
    exact Complex.ofReal_re _
  -- differentiate the real description directly
  have hpole : HasDerivAt (fun x : ℝ => 1 / (x - 1)) (-(1 / (s - 1) ^ 2)) s := by
    have hne : s - 1 ≠ 0 := by intro h; linarith
    have h := ((hasDerivAt_id s).sub_const 1).inv (by simpa using hne)
    simp only [id_eq] at h
    have hf : (fun x : ℝ => x - 1)⁻¹ = fun x : ℝ => 1 / (x - 1) := by
      funext x
      simp [one_div]
    rw [hf] at h
    have harith : -(1 / (s - 1) ^ 2) = -1 / (s - 1) ^ 2 := by ring
    rw [harith]
    exact h
  have hdirect : HasDerivAt (fun x : ℝ => (∑' n : ℕ, ((n:ℝ) + 1) ^ (-x)) - 1 / (x - 1))
      (zetaRderiv s + 1 / (s - 1) ^ 2) s := by
    have h := (zetaR_hasDerivAt s hs1).sub hpole
    have hf : ((fun t : ℝ => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-t)) - fun x : ℝ => 1 / (x - 1))
        = fun x : ℝ => (∑' n : ℕ, ((n:ℝ) + 1) ^ (-x)) - 1 / (x - 1) := by
      funext x
      rfl
    rw [hf] at h
    have harith2 : zetaRderiv s + 1 / (s - 1) ^ 2
        = zetaRderiv s - -(1 / (s - 1) ^ 2) := by ring
    rw [harith2]
    exact h
  -- the two descriptions agree near s, so the derivatives agree
  have hcongr : HasDerivAt (fun x : ℝ => (zetaRegFull ((x:ℂ))).re)
      (zetaRderiv s + 1 / (s - 1) ^ 2) s := by
    apply hdirect.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hs1] with x hx
    exact hrestrict x hx
  have huniq := hcongr.unique hreal
  rw [huniq]
  calc |(deriv zetaRegFull ((s:ℂ))).re| ≤ ‖deriv zetaRegFull ((s:ℂ))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖deriv zetaRegFull 1‖ + 1 := hcont _ hsball

/-- The Jacobian of the substitution: zeta/(-zeta') = eps (1 + O(eps)). -/
theorem jacobian_expansion :
    ∃ C > 0, ∃ r > 0, ∀ s : ℝ, 1 < s → s - 1 ≤ r →
      |(∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) / (-zetaRderiv s) - (s - 1)|
        ≤ C * (s - 1) ^ 2 := by
  obtain ⟨C2, hC2, r2, hr2, hB⟩ := zetaRderiv_pole_bound
  obtain ⟨C1, hC1, r1, hr1, hr1le, hA⟩ := eps_zeta_uniform
  -- A - eps B = gamma + O(eps), and 1/B <= 2 eps^2 for eps small
  refine ⟨2 * (|Real.eulerMascheroniConstant| + C1 + C2), by positivity,
    min (min r1 r2) (1 / (2 * (C2 + 1))), by positivity, ?_⟩
  intro s hs1 hsr
  set eps := s - 1 with heps
  have heps0 : 0 < eps := by rw [heps]; linarith
  have hr1' : eps ≤ r1 := le_trans hsr (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr2' : eps ≤ r2 := le_trans hsr (le_trans (min_le_left _ _) (min_le_right _ _))
  have hsmall : eps ≤ 1 / (2 * (C2 + 1)) := le_trans hsr (min_le_right _ _)
  set A := ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) with hA_def
  set B := -zetaRderiv s with hB_def
  -- from eps_zeta_uniform: |eps A - 1 - gamma eps| <= C1 eps^2
  have hAb : |eps * A - 1 - Real.eulerMascheroniConstant * eps| ≤ C1 * eps ^ 2 := by
    have h := hA eps heps0 hr1'
    have hse : (1 : ℝ) + eps = s := by rw [heps]; ring
    rw [hse] at h
    exact h
  -- from zetaRderiv_pole_bound: |B - 1/eps^2| <= C2
  have hBb : |B - 1 / eps ^ 2| ≤ C2 := by
    have h := hB s hs1 (by rw [← heps]; exact hr2')
    rw [hB_def]
    have hrw : -zetaRderiv s - 1 / eps ^ 2 = -(zetaRderiv s + 1 / eps ^ 2) := by ring
    rw [hrw, abs_neg, heps]
    exact h
  -- B >= 1/eps^2 - C2 > 0, and A - eps B = gamma + O(eps)
  have hBpos : 0 < B := by
    have hb1 : 1 / eps ^ 2 - C2 ≤ B := by
      have := abs_le.mp hBb
      linarith [this.1]
    have hlarge : C2 + 1 ≤ 1 / eps ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : eps * (2 * (C2 + 1)) ≤ 1 := by
        rw [← le_div_iff₀ (by positivity)]
        exact hsmall
      nlinarith [heps0, hC2]
    linarith
  have hnum : |A - eps * B| ≤ |Real.eulerMascheroniConstant| + C1 + C2 := by
    -- eps * (A - eps B) = (eps A - 1 - gamma eps) + gamma eps - eps^2 (B - 1/eps^2)
    have hid : eps * (A - eps * B)
        = (eps * A - 1 - Real.eulerMascheroniConstant * eps)
          + Real.eulerMascheroniConstant * eps - eps ^ 2 * (B - 1 / eps ^ 2) := by
      field_simp
      ring
    have hb1 := abs_le.mp hAb
    have hb2 := abs_le.mp hBb
    have heps1 : eps ≤ 1 := by
      have : (1:ℝ) / (2 * (C2 + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith [hsmall]
    -- bound eps * (A - eps B) first, then divide by eps
    have hprod : |eps * (A - eps * B)|
        ≤ eps * (|Real.eulerMascheroniConstant| + C1 + C2) := by
      rw [hid]
      have hb1a := hb1.1
      have hb1b := hb1.2
      have hb2a := hb2.1
      have hb2b := hb2.2
      have hg1 := le_abs_self Real.eulerMascheroniConstant
      have hg2 := neg_abs_le Real.eulerMascheroniConstant
      have hsq : eps ^ 2 ≤ eps := by nlinarith [heps0, heps1]
      have hp1 : C1 * eps ^ 2 ≤ C1 * eps :=
        mul_le_mul_of_nonneg_left hsq (le_of_lt hC1)
      have hp2 : eps ^ 2 * C2 ≤ eps * C2 :=
        mul_le_mul_of_nonneg_right hsq (le_of_lt hC2)
      have hp3 : Real.eulerMascheroniConstant * eps ≤ |Real.eulerMascheroniConstant| * eps :=
        mul_le_mul_of_nonneg_right hg1 (le_of_lt heps0)
      have hp4 : -(|Real.eulerMascheroniConstant| * eps)
          ≤ Real.eulerMascheroniConstant * eps := by
        have := mul_le_mul_of_nonneg_right hg2 (le_of_lt heps0)
        linarith
      have hBterm : |eps ^ 2 * (B - 1 / eps ^ 2)| ≤ eps * C2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ eps ^ 2)]
        calc eps ^ 2 * |B - 1 / eps ^ 2| ≤ eps ^ 2 * C2 :=
              mul_le_mul_of_nonneg_left hBb (by positivity)
          _ ≤ eps * C2 := hp2
      have hBt := abs_le.mp hBterm
      rw [abs_le]
      constructor
      · linarith [hb1a, hp1, hp4, hBt.2]
      · linarith [hb1b, hp1, hp3, hBt.1]
    rw [abs_mul, abs_of_pos heps0] at hprod
    exact le_of_mul_le_mul_left (by linarith [hprod]) heps0
  have hBlarge : 1 / (2 * eps ^ 2) ≤ B := by
    have hb1 := (abs_le.mp hBb).1
    have heps2 : (0:ℝ) < eps ^ 2 := by positivity
    have hhalf : 1 / (2 * eps ^ 2) + C2 ≤ 1 / eps ^ 2 := by
      rw [← sub_nonneg]
      have hexp : 1 / eps ^ 2 - (1 / (2 * eps ^ 2) + C2)
          = (1 - 2 * C2 * eps ^ 2) / (2 * eps ^ 2) := by
        field_simp
        ring
      rw [hexp]
      apply div_nonneg _ (by positivity)
      have hb : eps * (2 * (C2 + 1)) ≤ 1 := by
        rw [← le_div_iff₀ (by positivity)]
        exact hsmall
      nlinarith [heps0, hC2, hb]
    linarith
  have hdiv : A / B - eps = (A - eps * B) / B := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
  calc |A - eps * B| ≤ |Real.eulerMascheroniConstant| + C1 + C2 := hnum
    _ ≤ 2 * (|Real.eulerMascheroniConstant| + C1 + C2) * eps ^ 2 * B := by
        have hBb2 : 1 / (2 * eps ^ 2) ≤ B := hBlarge
        have hpos : (0:ℝ) < |Real.eulerMascheroniConstant| + C1 + C2 := by positivity
        have hkey : (1:ℝ) ≤ 2 * eps ^ 2 * B := by
          have h2 := mul_le_mul_of_nonneg_left hBb2
            (by positivity : (0:ℝ) ≤ 2 * eps ^ 2)
          calc (1:ℝ) = 2 * eps ^ 2 * (1 / (2 * eps ^ 2)) := by field_simp
            _ ≤ 2 * eps ^ 2 * B := h2
        nlinarith [hkey, hpos]

/-- The inverse of u = log zeta on (1, inf), as a function (0, inf) -> (1, inf). -/
noncomputable def sOf (u : ℝ) : ℝ := Function.invFunOn uOf (Set.Ioi 1) u

/-- sOf is a left inverse on (1, inf). -/
theorem sOf_uOf (s : ℝ) (hs : 1 < s) : sOf (uOf s) = s :=
  uOf_strictAnti.injOn.leftInvOn_invFunOn hs

/-- sOf lands in (1, inf) for u > 0. -/
theorem sOf_mem (u : ℝ) (hu : 0 < u) : 1 < sOf u := by
  have hmem : u ∈ uOf '' (Set.Ioi 1) := by rw [uOf_image]; exact hu
  exact Function.invFunOn_mem hmem

/-- uOf is a right inverse on (0, inf). -/
theorem uOf_sOf (u : ℝ) (hu : 0 < u) : uOf (sOf u) = u := by
  have hmem : u ∈ uOf '' (Set.Ioi 1) := by rw [uOf_image]; exact hu
  exact Function.invFunOn_eq hmem

/-- The change of variables in the direction the assembly needs:

    int_{Ioi 1} F(s) ds = int_{Ioi 0} F(sOf u) * J(u) du

where J(u) = 1/|u'(sOf u)| = zeta(sOf u) / (-zeta'(sOf u)) is the Jacobian,
which jacobian_expansion bounds as (sOf u - 1) + O((sOf u - 1)^2). -/
theorem integral_substitute (F : ℝ → ℝ) :
    (∫ s in Set.Ioi (1:ℝ), F s)
      = ∫ u in Set.Ioi (0:ℝ),
          F (sOf u) * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))) := by
  rw [uOf_change_of_variables
    (fun u => F (sOf u) * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hs1 : (1:ℝ) < s := hs
  simp only
  rw [sOf_uOf s hs1]
  -- |u'(s)| = -zeta'(s)/zeta(s), so |u'| * (zeta / (-zeta')) = 1
  have hzpos : (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
    have hsummable : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s)) := by
      have hb := Real.summable_nat_rpow.mpr (by linarith : (-s:ℝ) < -1)
      apply ((summable_nat_add_iff 1).mpr hb).congr
      intro n
      push_cast
      ring_nf
    have hle := hsummable.le_tsum 0 (fun n _ => by positivity)
    calc (0:ℝ) < ((0:ℝ) + 1) ^ (-s) := by norm_num
      _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by simpa using hle
  -- zeta' < 0 since zeta is strictly decreasing
  have hderivneg : zetaRderiv s < 0 := by
    unfold zetaRderiv
    have hsum := log_rpow_summable s hs1
    have hneg : (∑' n : ℕ, (-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-s))
        = -∑' n : ℕ, Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-s) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      ring
    rw [hneg, neg_lt_zero]
    -- the n = 1 term is positive, the rest nonneg
    have hterm : (0:ℝ) < Real.log (((1:ℕ):ℝ) + 1) * (((1:ℕ):ℝ) + 1) ^ (-s) := by
      apply mul_pos
      · apply Real.log_pos
        norm_num
      · positivity
    have hle := hsum.le_tsum 1 (fun n _ => by
      apply mul_nonneg _ (by positivity)
      apply Real.log_nonneg
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith)
    linarith
  have habs : |zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))|
      = -zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) := by
    rw [abs_div, abs_of_pos hzpos, abs_of_neg hderivneg]
  rw [habs]
  have hdne : zetaRderiv s ≠ 0 := ne_of_lt hderivneg
  field_simp

/-- fOdd in u-coordinates: the expansion's powers are now exact powers of the
integration variable, since uOf (sOf u) = u. -/
theorem fOdd_u_form (k : ℕ) (hk : 1 ≤ k)
    (hsum1 : Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n)))
    (hsum : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - zOmegaHom s z (p : ℕ))⁻¹))
    (hcd1 : ∀ s : ℝ, 1 < s →
      ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ∀ s : ℝ, 1 < s → ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0) :
    fOdd k = ∫ u in Set.Ioi (0:ℝ),
      (∑ j ∈ Finset.range (k + 1),
        (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
      * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))) := by
  rw [fOdd_eq_integral_FkOdd k hk hsum1]
  rw [integral_substitute (fun s => FkOdd k s)]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : (0:ℝ) < u := hu
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  simp only
  congr 1
  -- FkOdd k (sOf u) = sum_j h_j(sOf u) u^{k-j}/(k-j)!, using uOf (sOf u) = u
  have hexp := FkOdd_expansion' k hk (sOf u) hs1
    (hsum _ hs1) (hmul3 _ hs1) (hcd1 _ hs1) (hcd2 _ hs1)
  rw [uOf_sOf u hu0] at hexp
  have hre := congrArg Complex.re hexp
  simp only [Complex.ofReal_re] at hre
  rw [hre, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hrw : hCoeff (sOf u) j * ((u : ℝ) : ℂ) ^ (k - j)
      / ((Nat.factorial (k - j) : ℕ) : ℂ)
      = hCoeff (sOf u) j
        * (((u ^ (k - j) / (Nat.factorial (k - j) : ℝ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hrw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- e^u = zeta(sOf u): the bridge between the u and eps variables. -/
theorem exp_u_eq_zetaR (u : ℝ) (hu : 0 < u) :
    Real.exp u = ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) := by
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu
  have hzpos := zetaR_pos (sOf u) hs1
  have huu := uOf_sOf u hu
  unfold uOf at huu
  calc Real.exp u = Real.exp (Real.log (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)))) := by
        rw [huu]
    _ = ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) := Real.exp_log hzpos


/-- The inverse expansion: eps(u) = s(u) - 1 satisfies |eps(u) - e^-u| <= C e^-2u.

From eps_zeta_uniform, e^u = zeta(1+eps) = (1 + gamma eps + O(eps^2))/eps,
so e^-u = eps/(1 + gamma eps + O(eps^2)) = eps(1 - gamma eps + O(eps^2)),
i.e. eps = e^-u + gamma e^-2u + O(e^-3u). -/
theorem eps_of_u_expansion :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |(sOf u - 1) - Real.exp (-u)| ≤ C * Real.exp (-2 * u) := by
  obtain ⟨C1, hC1, r1, hr1, hr1le, hA⟩ := eps_zeta_uniform
  -- for u large, eps(u) = sOf u - 1 is small
  have hepssmall : ∃ U0 > 0, ∀ u : ℝ, U0 ≤ u → sOf u - 1 ≤ r1 := by
    -- sOf is antitone (inverse of an antitone map), so sOf u <= sOf U0 for u >= U0.
    -- Choose U0 = uOf (1 + r1), so sOf U0 = 1 + r1.
    have hr1pos : (0:ℝ) < 1 + r1 - 1 := by linarith
    have hmem : (1:ℝ) < 1 + r1 := by linarith
    refine ⟨uOf (1 + r1), ?_, ?_⟩
    · unfold uOf
      exact Real.log_pos (zetaR_gt_one (1 + r1) hmem)
    · intro u hu
      by_contra hcon
      push_neg at hcon
      have hgt : (1:ℝ) + r1 < sOf u := by linarith
      have hu0 : (0:ℝ) < u := by
        have hU0pos : (0:ℝ) < uOf (1 + r1) := Real.log_pos (zetaR_gt_one (1 + r1) hmem)
        linarith
      have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
      have hanti := uOf_strictAnti (Set.mem_Ioi.mpr hmem) (Set.mem_Ioi.mpr hs1) hgt
      rw [uOf_sOf u hu0] at hanti
      linarith
  obtain ⟨U0, hU0, hsmall⟩ := hepssmall
  -- the key identity: eps * e^u = 1 + gamma eps + O(eps^2)
  -- e^u = zeta(sOf u), since u = uOf (sOf u) = log zeta (sOf u)
  have hexpu : ∀ u : ℝ, 0 < u →
      Real.exp u = ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) := by
    intro u hu
    have hs1 : (1:ℝ) < sOf u := sOf_mem u hu
    have hzpos : (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) := by
      have hsm : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-(sOf u))) := by
        have hb := Real.summable_nat_rpow.mpr (by linarith : (-(sOf u):ℝ) < -1)
        apply ((summable_nat_add_iff 1).mpr hb).congr
        intro n
        push_cast
        ring_nf
      have hle := hsm.le_tsum 0 (fun n _ => by positivity)
      calc (0:ℝ) < ((0:ℝ) + 1) ^ (-(sOf u)) := by norm_num
        _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) := by simpa using hle
    have huu := uOf_sOf u hu
    unfold uOf at huu
    calc Real.exp u = Real.exp (Real.log (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)))) := by
          rw [huu]
      _ = ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) := Real.exp_log hzpos
  refine ⟨(|Real.eulerMascheroniConstant| + C1) * (1 + |Real.eulerMascheroniConstant| + C1), by positivity, U0, hU0, ?_⟩
  intro u hUu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU0 hUu
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  set eps := sOf u - 1 with hepsdef
  have heps0 : 0 < eps := by rw [hepsdef]; linarith
  have hepsr : eps ≤ r1 := hsmall u hUu
  -- eps * e^u = 1 + gamma eps + O(eps^2)
  have hone : (1:ℝ) + eps = sOf u := by rw [hepsdef]; ring
  have hprod : |eps * Real.exp u - 1 - Real.eulerMascheroniConstant * eps|
      ≤ C1 * eps ^ 2 := by
    rw [exp_u_eq_zetaR u hu0, ← hone]
    exact hA eps heps0 hepsr
  have hexppos : (0:ℝ) < Real.exp u := Real.exp_pos u
  have hb := abs_le.mp hprod
  -- |eps e^u - 1| <= (|gamma| + C1) eps  (using eps <= 1)
  have heps1 : eps ≤ 1 := le_trans hepsr hr1le
  have hmid : |eps * Real.exp u - 1| ≤ (|Real.eulerMascheroniConstant| + C1) * eps := by
    have hg1 := le_abs_self Real.eulerMascheroniConstant
    have hg2 := neg_abs_le Real.eulerMascheroniConstant
    have hsq : eps ^ 2 ≤ eps := by nlinarith [heps0, heps1]
    rw [abs_le]
    constructor <;> nlinarith [hb.1, hb.2, hsq, hC1, heps0,
      mul_le_mul_of_nonneg_right hg1 (le_of_lt heps0),
      mul_le_mul_of_nonneg_right hg2 (le_of_lt heps0)]
  -- so |eps - e^-u| = |eps e^u - 1| e^-u <= (|gamma| + C1) eps e^-u
  have hfac : |eps - Real.exp (-u)| = |eps * Real.exp u - 1| * Real.exp (-u) := by
    have hid : eps - Real.exp (-u) = (eps * Real.exp u - 1) * Real.exp (-u) := by
      rw [Real.exp_neg]
      field_simp
    rw [hid, abs_mul, abs_of_pos (Real.exp_pos (-u))]
  -- bootstrap: eps <= 2 e^-u, from |eps e^u - 1| <= (|gamma|+C1) eps and eps small
  have hboot : eps ≤ (1 + |Real.eulerMascheroniConstant| + C1) * Real.exp (-u) := by
    have hm := abs_le.mp hmid
    have hup : eps * Real.exp u ≤ 1 + (|Real.eulerMascheroniConstant| + C1) * eps := by
      linarith [hm.2]
    have hup2 : eps * Real.exp u ≤ 1 + (|Real.eulerMascheroniConstant| + C1) := by
      nlinarith [heps1, heps0, abs_nonneg Real.eulerMascheroniConstant, hC1]
    rw [← le_div_iff₀ (Real.exp_pos u)] at hup2
    rw [Real.exp_neg]
    calc eps ≤ (1 + (|Real.eulerMascheroniConstant| + C1)) / Real.exp u := hup2
      _ = (1 + |Real.eulerMascheroniConstant| + C1) * (Real.exp u)⁻¹ := by
          rw [div_eq_mul_inv]; ring_nf
  -- combine
  rw [hfac]
  calc |eps * Real.exp u - 1| * Real.exp (-u)
      ≤ ((|Real.eulerMascheroniConstant| + C1) * eps) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hmid (le_of_lt (Real.exp_pos (-u)))
    _ ≤ ((|Real.eulerMascheroniConstant| + C1) * ((1 + |Real.eulerMascheroniConstant| + C1) * Real.exp (-u))) * Real.exp (-u) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos (-u)))
        apply mul_le_mul_of_nonneg_left hboot (by positivity)
    _ = (|Real.eulerMascheroniConstant| + C1) * (1 + |Real.eulerMascheroniConstant| + C1) * Real.exp (-2 * u) := by
        rw [show (-2 * u : ℝ) = -u + -u by ring, Real.exp_add]
        ring

/-- The crude bound eps(u) <= C e^-u, extracted for reuse. -/
theorem eps_of_u_bound :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u → sOf u - 1 ≤ C * Real.exp (-u) := by
  obtain ⟨C, hC, U, hU, hexp⟩ := eps_of_u_expansion
  refine ⟨C + 1, by positivity, U, hU, ?_⟩
  intro u hUu
  have h := abs_le.mp (hexp u hUu)
  have he2 : Real.exp (-2 * u) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU hUu
    linarith
  have hepos : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  nlinarith [h.2, he2, hC, hepos]

/-- STEP A: the Jacobian is e^-u + O(e^-2u).

Composes jacobian_expansion (J = eps + O(eps^2)) with eps_of_u_expansion
(eps = e^-u + O(e^-2u)). -/
theorem jacobian_u_form :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - Real.exp (-u)| ≤ C * Real.exp (-2 * u) := by
  obtain ⟨CJ, hCJ, rJ, hrJ, hJ⟩ := jacobian_expansion
  obtain ⟨CE, hCE, UE, hUE, hE⟩ := eps_of_u_expansion
  obtain ⟨CB, hCB, UB, hUB, hB⟩ := eps_of_u_bound
  -- for u large, eps(u) <= rJ and eps(u) <= CB e^-u
  have hUr : ∃ U1 > 0, ∀ u : ℝ, U1 ≤ u → sOf u - 1 ≤ rJ := by
    -- eps <= CB e^-u, and CB e^-u <= rJ once u >= log (CB / rJ)
    refine ⟨max UB (Real.log (CB / rJ) + 1), by positivity, ?_⟩
    intro u hu
    have huB : UB ≤ u := le_trans (le_max_left _ _) hu
    have hlog : Real.log (CB / rJ) + 1 ≤ u := le_trans (le_max_right _ _) hu
    have hb := hB u huB
    have hexp : CB * Real.exp (-u) ≤ rJ := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos u)]
      calc CB = rJ * (CB / rJ) := by field_simp
        _ ≤ rJ * Real.exp u := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hrJ)
            calc CB / rJ = Real.exp (Real.log (CB / rJ)) :=
                  (Real.exp_log (by positivity)).symm
              _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    linarith
  obtain ⟨U1, hU1, hr⟩ := hUr
  refine ⟨CJ * CB ^ 2 + CE, by positivity,
    max (max UE UB) U1, by positivity, ?_⟩
  intro u hu
  have huE : UE ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have huB : UB ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu1 : U1 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU1 hu1
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  set J := (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)) with hJdef
  set eps := sOf u - 1 with hepsdef
  have h1 : |J - eps| ≤ CJ * eps ^ 2 := hJ (sOf u) hs1 (hr u hu1)
  have h2 : |eps - Real.exp (-u)| ≤ CE * Real.exp (-2 * u) := hE u huE
  have h3 : eps ≤ CB * Real.exp (-u) := hB u huB
  have heps0 : 0 ≤ eps := by rw [hepsdef]; linarith
  have hsq : eps ^ 2 ≤ CB ^ 2 * Real.exp (-2 * u) := by
    have hexp2 : Real.exp (-u) * Real.exp (-u) = Real.exp (-2 * u) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [h3, heps0, Real.exp_pos (-u), hCB]
  have htri : |J - Real.exp (-u)| ≤ |J - eps| + |eps - Real.exp (-u)| := by
    have hid : J - Real.exp (-u) = (J - eps) + (eps - Real.exp (-u)) := by ring
    rw [hid]
    exact abs_add_le _ _
  have hmul : CJ * eps ^ 2 ≤ CJ * (CB ^ 2 * Real.exp (-2 * u)) :=
    mul_le_mul_of_nonneg_left hsq (le_of_lt hCJ)
  calc |J - Real.exp (-u)| ≤ |J - eps| + |eps - Real.exp (-u)| := htri
    _ ≤ CJ * (CB ^ 2 * Real.exp (-2 * u)) + CE * Real.exp (-2 * u) := by linarith
    _ = (CJ * CB ^ 2 + CE) * Real.exp (-2 * u) := by ring

/-- The signed second-order expansion of the coefficients:

    h_j(s) = h_j(1) + (s-1) b_j + R_j(s),   |R_j(s)| <= betaS (s-1)^2 / 2

This is what step D needs -- the first-order term is the leading correction,
not an error to be bounded away.  Applies taylor_second_bound from the main
development. -/
theorem hCoeff_taylor (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd) (j : ℕ)
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    ‖hCoeff s j - hCoeff 1 j - (((s - 1 : ℝ)) : ℂ) * bHatOdd j‖
      ≤ betaFam j * (s - 1) ^ 2 / 2 :=
  taylor_second_bound (fun t => hCoeff t j) (hCoeff 1 j) (bHatOdd j) (betaFam j) (hf.nonneg j)
    (fun x hx => hf.deriv_exists j x hx)
    (fun x hx => hf.deriv2_exists j x hx)
    (fun x hx => hf.deriv2_bound j x hx)
    (hf.tendsto_one j) (hf.tendsto_deriv j) s hs

/-- STEP B: the coefficients at s(u) differ from those at 1 by O(e^-u),
uniformly in j.

Composes hCoeff_lipschitz (|h_j(s) - h_j(t)| <= betaS |s - t|) with
eps_of_u_bound (s(u) - 1 <= C e^-u).  Note h_j(1) is the limiting value; the
Lipschitz bound is stated on (1,2), so this is |h_j(s(u)) - h_j(1+delta)| for
delta small, and h_j(1) enters as the limit. -/
theorem hCoeff_sub_one_bound (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd) (j : ℕ)
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    ‖hCoeff s j - hCoeff 1 j‖ ≤ betaFam j * (s - 1) :=
  deriv_sub_limit_bound (fun t => hCoeff t j) (hCoeff 1 j) (betaFam j) (hf.nonneg j)
    (fun x hx => hf.deriv_exists j x hx) (fun x hx => hf.deriv_bound j x hx)
    (hf.tendsto_one j) s hs

theorem hCoeff_u_form (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd) (j : ℕ) :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      ‖hCoeff (sOf u) j - hCoeff 1 j‖ ≤ C * Real.exp (-u) := by
  obtain ⟨CB, hCB, UB, hUB, hB⟩ := eps_of_u_bound
  -- need sOf u < 2 as well, which holds for u large
  have hUlt : ∃ U2 > 0, ∀ u : ℝ, U2 ≤ u → sOf u < 2 := by
    refine ⟨max UB (Real.log CB + 1), by positivity, ?_⟩
    intro u hu
    have huB : UB ≤ u := le_trans (le_max_left _ _) hu
    have hlog : Real.log CB + 1 ≤ u := le_trans (le_max_right _ _) hu
    have hb := hB u huB
    have hexp : CB * Real.exp (-u) < 1 := by
      rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos u)]
      calc CB = Real.exp (Real.log CB) := (Real.exp_log hCB).symm
        _ < Real.exp u := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 * Real.exp u := by ring
    linarith
  obtain ⟨U2, hU2, hlt2⟩ := hUlt
  have hpos : (0:ℝ) < betaFam j * CB + 1 := by
    have : (0:ℝ) ≤ betaFam j * CB := mul_nonneg (hf.nonneg j) (le_of_lt hCB)
    linarith
  refine ⟨betaFam j * CB + 1, hpos, max UB U2, by positivity, ?_⟩
  intro u hu
  have huB : UB ≤ u := le_trans (le_max_left _ _) hu
  have hu2 : U2 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hUB huB
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  have hsmem : sOf u ∈ Set.Ioo (1:ℝ) 2 := ⟨hs1, hlt2 u hu2⟩
  have hlip := hCoeff_sub_one_bound betaFam bHatOdd hf j (sOf u) hsmem
  have hb := hB u huB
  calc ‖hCoeff (sOf u) j - hCoeff 1 j‖ ≤ betaFam j * (sOf u - 1) := hlip
    _ ≤ betaFam j * (CB * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left hb (hf.nonneg j)
    _ ≤ (betaFam j * CB + 1) * Real.exp (-u) := by
        have := Real.exp_pos (-u)
        nlinarith [this]

/-! ### Signed second-order data for zeta near the pole

`zetaRegFull` is analytic at 1 (zetaRegFull_analyticAt_one), hence twice
differentiable there.  Writing c1 = deriv zetaRegFull 1 (which equals -gamma_1,
the second Stieltjes constant, though we never need that identification):

    zeta(s) = 1/(s-1) + gamma + c1 (s-1) + O((s-1)^2)

This is the signed refinement of zetaRegFull_taylor_bound, and it is what the
signed Jacobian expansion needs. -/

/-- The real second-order expansion of zeta near 1. -/
theorem zetaR_second_order :
    ∃ C > 0, ∃ r > 0, ∀ s : ℝ, 1 < s → s - 1 ≤ r →
      |(∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1)
        - Real.eulerMascheroniConstant
        - (s - 1) * (deriv zetaRegFull 1).re| ≤ C * (s - 1) ^ 2 := by
  obtain ⟨C, hC, r, hr, htay⟩ := zetaRegFull_taylor_bound
  refine ⟨C, hC, min r 1, by positivity, ?_⟩
  intro s hs1 hsr
  have hsr' : s - 1 ≤ r := le_trans hsr (min_le_left _ _)
  have hne : ((s:ℂ)) ≠ 1 := by
    intro hc
    have : (s:ℝ) = 1 := by exact_mod_cast hc
    linarith
  have hnorm : ‖((s:ℂ)) - 1‖ = s - 1 := by
    have hid : ((s:ℂ)) - 1 = (((s - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h := htay ((s:ℂ)) (by rw [hnorm]; exact hsr')
  rw [hnorm, zetaRegFull_one_eq_gamma] at h
  -- take real parts; zetaRegFull(s) is real for real s > 1
  have hre : (zetaRegFull ((s:ℂ))).re
      = (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1) := by
    rw [zetaRegFull_eq_of_ne _ hne]
    unfold zetaReg
    rw [← zeta_series_eq s hs1]
    have hsub : ((s:ℂ)) - 1 = (((s - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub]
    exact Complex.ofReal_re _
  -- the real part of the complex Taylor remainder is the real remainder
  have hrepart : ((zetaRegFull ((s:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
      - deriv zetaRegFull 1 * (((s:ℂ)) - 1))).re
      = (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1)
        - Real.eulerMascheroniConstant - (s - 1) * (deriv zetaRegFull 1).re := by
    have hsub : ((s:ℂ)) - 1 = (((s - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hsub]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      hre]
    ring
  calc |(∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) - 1 / (s - 1)
        - Real.eulerMascheroniConstant - (s - 1) * (deriv zetaRegFull 1).re|
      = |((zetaRegFull ((s:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
          - deriv zetaRegFull 1 * (((s:ℂ)) - 1))).re| := by rw [hrepart]
    _ ≤ ‖zetaRegFull ((s:ℂ)) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
          - deriv zetaRegFull 1 * (((s:ℂ)) - 1)‖ := Complex.abs_re_le_norm _
    _ ≤ C * (s - 1) ^ 2 := h

/-- The derivative of zetaRegFull is Lipschitz near 1 (it is analytic there,
hence its derivative is continuous and locally Lipschitz). -/
theorem zetaRegFull_deriv_lipschitz :
    ∃ C > 0, ∃ r > 0, ∀ s : ℝ, 1 < s → s - 1 ≤ r →
      ‖deriv zetaRegFull ((s:ℂ)) - deriv zetaRegFull 1‖ ≤ C * (s - 1) := by
  have hana : AnalyticAt ℂ (deriv zetaRegFull) 1 := zetaRegFull_analyticAt_one.deriv
  have hps := hana.hasFPowerSeriesAt
  have hO := hps.isBigO_sub_partialSum_pow 1
  obtain ⟨C, hC, hbw⟩ := hO.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hbw
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hbw
  refine ⟨C, hC, r / 2, by linarith, ?_⟩
  intro s hs1 hsr
  have hy : ((s:ℂ)) - 1 ∈ Metric.ball (0:ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    have hid : ((s:ℂ)) - 1 = (((s - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hb := hrsub hy
  simp only [Set.mem_setOf_eq] at hb
  have hadd : (1 : ℂ) + (((s:ℂ)) - 1) = (s:ℂ) := by ring
  rw [hadd] at hb
  have hpart : (FormalMultilinearSeries.ofScalars ℂ
      fun n => iteratedDeriv n (deriv zetaRegFull) 1 / (Nat.factorial n : ℂ)).partialSum 1
      (((s:ℂ)) - 1) = deriv zetaRegFull 1 := by
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_one]
    simp [FormalMultilinearSeries.ofScalars, iteratedDeriv_zero]
  rw [hpart] at hb
  have hn : ‖((s:ℂ)) - 1‖ ^ 1 = s - 1 := by
    have hid : ((s:ℂ)) - 1 = (((s - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), pow_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hn] at hb
  exact hb

/-- The signed second-order expansion of -zeta':

    -zeta'(s) = 1/(s-1)^2 - c1 + O(s-1),   c1 = (deriv zetaRegFull 1).re -/
theorem zetaRderiv_second_order :
    ∃ C > 0, ∃ r > 0, ∀ s : ℝ, 1 < s → s - 1 ≤ r →
      |(-zetaRderiv s) - 1 / (s - 1) ^ 2 + (deriv zetaRegFull 1).re|
        ≤ C * (s - 1) := by
  obtain ⟨C, hC, r, hr, hlip⟩ := zetaRegFull_deriv_lipschitz
  refine ⟨C, hC, r, hr, ?_⟩
  intro s hs1 hsr
  -- from zetaRderiv_pole_bound's derivative identification:
  --   zetaRderiv s + 1/(s-1)^2 = (deriv zetaRegFull s).re
  have hid : zetaRderiv s + 1 / (s - 1) ^ 2 = (deriv zetaRegFull ((s:ℂ))).re :=
    zetaRderiv_eq_re s hs1
  have hrw : (-zetaRderiv s) - 1 / (s - 1) ^ 2 + (deriv zetaRegFull 1).re
      = -((zetaRderiv s + 1 / (s - 1) ^ 2) - (deriv zetaRegFull 1).re) := by ring
  rw [hrw, abs_neg, hid]
  calc |(deriv zetaRegFull ((s:ℂ))).re - (deriv zetaRegFull 1).re|
      = |(deriv zetaRegFull ((s:ℂ)) - deriv zetaRegFull 1).re| := by
        rw [Complex.sub_re]
    _ ≤ ‖deriv zetaRegFull ((s:ℂ)) - deriv zetaRegFull 1‖ := Complex.abs_re_le_norm _
    _ ≤ C * (s - 1) := hlip s hs1 hsr

/-- The signed Jacobian expansion in s:

    zeta/(-zeta') = eps + gamma eps^2 + O(eps^3),   eps = s - 1

Verified symbolically: dividing zeta = 1/eps + gamma + c1 eps + O(eps^2) by
-zeta' = 1/eps^2 - c1 + O(eps) gives eps + gamma eps^2 + 2 c1 eps^3 + ... -/
theorem jacobian_signed :
    ∃ C > 0, ∃ r > 0, ∀ s : ℝ, 1 < s → s - 1 ≤ r →
      |(∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) / (-zetaRderiv s)
        - (s - 1) - Real.eulerMascheroniConstant * (s - 1) ^ 2|
        ≤ C * (s - 1) ^ 3 := by
  obtain ⟨CA, hCA, rA, hrA, hA⟩ := zetaR_second_order
  obtain ⟨CB, hCB, rB, hrB, hB⟩ := zetaRderiv_second_order
  set c1 := (deriv zetaRegFull 1).re with hc1
  set c1 := (deriv zetaRegFull 1).re with hc1
  set G := Real.eulerMascheroniConstant with hG
  set K := CA + CB * (1 + |G|) + 2 * |c1| + |c1| * |G| with hK
  have hKpos : 0 < K := by
    rw [hK]
    have : (0:ℝ) ≤ CB * (1 + |G|) := by positivity
    have h2 : (0:ℝ) ≤ 2 * |c1| := by positivity
    have h3 : (0:ℝ) ≤ |c1| * |G| := by positivity
    linarith
  refine ⟨2 * K, by positivity,
    min (min rA rB) (min 1 (1 / (2 * (|c1| + CB + 1)))), by positivity, ?_⟩
  intro s hs1 hsr
  set eps := s - 1 with hepsdef
  have heps0 : 0 < eps := by rw [hepsdef]; linarith
  have hepsA : eps ≤ rA := le_trans hsr (le_trans (min_le_left _ _) (min_le_left _ _))
  have hepsB : eps ≤ rB := le_trans hsr (le_trans (min_le_left _ _) (min_le_right _ _))
  have heps1 : eps ≤ 1 :=
    le_trans hsr (le_trans (min_le_right _ _) (min_le_left _ _))
  have hepsB2 : eps ≤ 1 / (2 * (|c1| + CB + 1)) :=
    le_trans hsr (le_trans (min_le_right _ _) (min_le_right _ _))
  set A := ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) with hAdef
  set B := -zetaRderiv s with hBdef
  have hAb : |A - 1 / eps - Real.eulerMascheroniConstant - eps * c1| ≤ CA * eps ^ 2 := by
    have h := hA s hs1 hepsA
    have hrw : A - 1 / eps - Real.eulerMascheroniConstant - eps * c1
        = A - 1 / (s - 1) - Real.eulerMascheroniConstant
          - (s - 1) * (deriv zetaRegFull 1).re := by
      rw [hepsdef, hc1]
    rw [hrw]
    exact h
  have hBb : |B - 1 / eps ^ 2 + c1| ≤ CB * eps := by
    have h := hB s hs1 hepsB
    have hrw : B - 1 / eps ^ 2 + c1
        = (-zetaRderiv s) - 1 / (s - 1) ^ 2 + (deriv zetaRegFull 1).re := by
      rw [hepsdef, hc1, hBdef]
    rw [hrw]
    exact h
  have hBlow : 1 / (2 * eps ^ 2) ≤ B := by
    have hb := (abs_le.mp hBb).1
    -- B >= 1/eps^2 - |c1| - CB eps, and eps <= 1/(2(|c1|+CB+1))
    have hc1le : -|c1| ≤ c1 := neg_abs_le c1
    have hstep : 1 / eps ^ 2 - |c1| - CB * eps ≤ B := by
      have := le_abs_self c1
      nlinarith [hb, hc1le, heps0]
    have hhalf : 1 / (2 * eps ^ 2) + |c1| + CB * eps ≤ 1 / eps ^ 2 := by
      have hexp : 1 / eps ^ 2 - 1 / (2 * eps ^ 2) = 1 / (2 * eps ^ 2) := by
        field_simp
        ring
      have hbig : |c1| + CB * eps ≤ 1 / (2 * eps ^ 2) := by
        have hle : eps * (2 * (|c1| + CB + 1)) ≤ 1 := by
          rw [← le_div_iff₀ (by positivity)]
          exact hepsB2
        rw [le_div_iff₀ (by positivity)]
        have h1 : |c1| + CB * eps ≤ |c1| + CB + 1 := by
          nlinarith [heps0, heps1, hCB.le]
        have h2 : (2:ℝ) * eps ^ 2 ≤ 2 * eps := by nlinarith [heps0, heps1]
        have h3 : (0:ℝ) ≤ |c1| + CB * eps := by positivity
        calc (|c1| + CB * eps) * (2 * eps ^ 2)
            ≤ (|c1| + CB + 1) * (2 * eps) := by
              apply mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = eps * (2 * (|c1| + CB + 1)) := by ring
          _ ≤ 1 := hle
      linarith
    linarith
  have hBpos : 0 < B := by
    have : (0:ℝ) < 1 / (2 * eps ^ 2) := by positivity
    linarith
  have hnumid : A - eps * B - G * eps ^ 2 * B
      = (A - 1 / eps - G - eps * c1)
        - (B - 1 / eps ^ 2 + c1) * (eps + G * eps ^ 2)
        + 2 * c1 * eps + c1 * G * eps ^ 2 := by
    field_simp
    ring
  have hsq : eps ^ 2 ≤ eps := by nlinarith [heps0, heps1]
  have hlin : |eps + G * eps ^ 2| ≤ (1 + |G|) * eps := by
    calc |eps + G * eps ^ 2| ≤ |eps| + |G * eps ^ 2| := abs_add_le _ _
      _ = eps + |G| * eps ^ 2 := by
          rw [abs_of_pos heps0, abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ eps ^ 2)]
      _ ≤ eps + |G| * eps := by
          have := mul_le_mul_of_nonneg_left hsq (abs_nonneg G)
          linarith
      _ = (1 + |G|) * eps := by ring
  have hfac : |(B - 1 / eps ^ 2 + c1) * (eps + G * eps ^ 2)|
      ≤ (CB * eps) * ((1 + |G|) * eps) := by
    rw [abs_mul]
    exact mul_le_mul hBb hlin (abs_nonneg _) (by positivity)
  have hlast : |2 * c1 * eps + c1 * G * eps ^ 2|
      ≤ (2 * |c1| + |c1| * |G|) * eps := by
    have h1 : |2 * c1 * eps| = 2 * |c1| * eps := by
      rw [abs_mul, abs_mul, abs_of_pos heps0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : |c1 * G * eps ^ 2| = |c1| * |G| * eps ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ eps ^ 2)]
    have h3 : |c1| * |G| * eps ^ 2 ≤ |c1| * |G| * eps :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    calc |2 * c1 * eps + c1 * G * eps ^ 2|
        ≤ |2 * c1 * eps| + |c1 * G * eps ^ 2| := abs_add_le _ _
      _ = 2 * |c1| * eps + |c1| * |G| * eps ^ 2 := by rw [h1, h2]
      _ ≤ 2 * |c1| * eps + |c1| * |G| * eps := by linarith
      _ = (2 * |c1| + |c1| * |G|) * eps := by ring
  have hA2 : CA * eps ^ 2 ≤ CA * eps :=
    mul_le_mul_of_nonneg_left hsq (le_of_lt hCA)
  have hnum : |A - eps * B - G * eps ^ 2 * B| ≤ K * eps := by
    rw [hnumid]
    set X := A - 1 / eps - G - eps * c1 with hX
    set Y := (B - 1 / eps ^ 2 + c1) * (eps + G * eps ^ 2) with hY
    set Z := 2 * c1 * eps + c1 * G * eps ^ 2 with hZ
    have hgoal : X - Y + 2 * c1 * eps + c1 * G * eps ^ 2 = (X - Y) + Z := by
      rw [hZ]; ring
    rw [hgoal]
    have t1 : |X - Y| ≤ |X| + |Y| := abs_sub _ _
    have t2 : |(X - Y) + Z| ≤ |X - Y| + |Z| := abs_add_le _ _
    have hXb : |X| ≤ CA * eps := le_trans hAb hA2
    have hYb : |Y| ≤ CB * (1 + |G|) * eps := by
      have hstep : CB * eps * ((1 + |G|) * eps) = (CB * (1 + |G|)) * eps ^ 2 := by ring
      rw [hstep] at hfac
      have := mul_le_mul_of_nonneg_left hsq
        (by positivity : (0:ℝ) ≤ CB * (1 + |G|))
      linarith [hfac, this]
    rw [hK]
    linarith [t1, t2, hXb, hYb, hlast]
  have hdivid : A / B - eps - G * eps ^ 2
      = (A - eps * B - G * eps ^ 2 * B) / B := by
    field_simp
  rw [hdivid, abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
  have hBinv : (1:ℝ) ≤ 2 * eps ^ 2 * B := by
    have h2 := mul_le_mul_of_nonneg_left hBlow
      (by positivity : (0:ℝ) ≤ 2 * eps ^ 2)
    calc (1:ℝ) = 2 * eps ^ 2 * (1 / (2 * eps ^ 2)) := by field_simp
      _ ≤ 2 * eps ^ 2 * B := h2
  have hKe : (0:ℝ) ≤ K * eps := by positivity
  have hstep : K * eps ≤ (K * eps) * (2 * eps ^ 2 * B) := by
    calc K * eps = (K * eps) * 1 := by ring
      _ ≤ (K * eps) * (2 * eps ^ 2 * B) := mul_le_mul_of_nonneg_left hBinv hKe
  calc |A - eps * B - G * eps ^ 2 * B| ≤ K * eps := hnum
    _ ≤ (K * eps) * (2 * eps ^ 2 * B) := hstep
    _ = 2 * K * eps ^ 3 * B := by ring
  

/-- The signed eps(u) expansion:

    eps(u) = e^-u + gamma e^-2u + O(e^-3u) -/
theorem eps_of_u_signed :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |(sOf u - 1) - Real.exp (-u)
        - Real.eulerMascheroniConstant * Real.exp (-2 * u)|
        ≤ C * Real.exp (-3 * u) := by
  obtain ⟨C1, hC1, r1, hr1, hr1le, hA⟩ := eps_zeta_uniform
  obtain ⟨CE, hCE, UE, hUE, hE⟩ := eps_of_u_expansion
  obtain ⟨CB, hCB, UB, hUB, hBd⟩ := eps_of_u_bound
  set G := Real.eulerMascheroniConstant with hG
  -- eps <= r1 for u large (same threshold argument as before)
  have hUr : ∃ U1 > 0, ∀ u : ℝ, U1 ≤ u → sOf u - 1 ≤ r1 := by
    refine ⟨max UB (Real.log (CB / r1) + 1), by positivity, ?_⟩
    intro u hu
    have huB : UB ≤ u := le_trans (le_max_left _ _) hu
    have hlog : Real.log (CB / r1) + 1 ≤ u := le_trans (le_max_right _ _) hu
    have hb := hBd u huB
    have hexp : CB * Real.exp (-u) ≤ r1 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos u)]
      calc CB = r1 * (CB / r1) := by field_simp
        _ ≤ r1 * Real.exp u := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hr1)
            calc CB / r1 = Real.exp (Real.log (CB / r1)) :=
                  (Real.exp_log (by positivity)).symm
              _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    linarith
  obtain ⟨U1, hU1, hr⟩ := hUr
  refine ⟨|G| * CE + C1 * CB ^ 2, by positivity,
    max (max UE UB) U1, by positivity, ?_⟩
  intro u hu
  have huE : UE ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have huB : UB ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu1 : U1 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU1 hu1
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  set eps := sOf u - 1 with hepsdef
  set x := Real.exp (-u) with hxdef
  have hxpos : 0 < x := Real.exp_pos _
  have heps0 : 0 < eps := by rw [hepsdef]; linarith
  have hr' : eps ≤ r1 := hr u hu1
  have hEb : |eps - x| ≤ CE * Real.exp (-2 * u) := hE u huE
  have hBb2 : eps ≤ CB * x := hBd u huB
  -- eps * e^u = 1 + G eps + a  with |a| <= C1 eps^2
  have hprod : |eps * Real.exp u - 1 - G * eps| ≤ C1 * eps ^ 2 := by
    have hone : (1:ℝ) + eps = sOf u := by rw [hepsdef]; ring
    rw [exp_u_eq_zetaR u hu0, ← hone]
    exact hA eps heps0 hr'
  -- eps = x(1 + G eps + a), so eps - x - G x^2 = G x (eps - x) + a x
  have hxe : x * Real.exp u = 1 := by
    rw [hxdef, Real.exp_neg]
    field_simp
  have hid : eps - x - G * x ^ 2
      = G * x * (eps - x) + (eps * Real.exp u - 1 - G * eps) * x := by
    have h1 : eps * Real.exp u * x = eps := by
      calc eps * Real.exp u * x = eps * (x * Real.exp u) := by ring
        _ = eps := by rw [hxe]; ring
    nlinarith [h1, hxe]
  have hx2 : Real.exp (-2 * u) = x ^ 2 := by
    rw [hxdef, ← Real.exp_nat_mul]
    ring_nf
  have hx3 : Real.exp (-3 * u) = x ^ 3 := by
    rw [hxdef, ← Real.exp_nat_mul]
    ring_nf
  rw [hx2, hx3, hid]
  -- |G x (eps - x)| <= |G| x CE x^2
  have t1 : |G * x * (eps - x)| ≤ |G| * CE * x ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos hxpos]
    have := hEb
    rw [hx2] at this
    calc |G| * x * |eps - x| ≤ |G| * x * (CE * x ^ 2) := by
          apply mul_le_mul_of_nonneg_left this (by positivity)
      _ = |G| * CE * x ^ 3 := by ring
  -- |a x| <= C1 eps^2 x <= C1 CB^2 x^3
  have t2 : |(eps * Real.exp u - 1 - G * eps) * x| ≤ C1 * CB ^ 2 * x ^ 3 := by
    rw [abs_mul, abs_of_pos hxpos]
    have heps2 : eps ^ 2 ≤ CB ^ 2 * x ^ 2 := by nlinarith [hBb2, heps0, hxpos]
    calc |eps * Real.exp u - 1 - G * eps| * x ≤ (C1 * eps ^ 2) * x :=
          mul_le_mul_of_nonneg_right hprod (le_of_lt hxpos)
      _ ≤ (C1 * (CB ^ 2 * x ^ 2)) * x := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hxpos)
          exact mul_le_mul_of_nonneg_left heps2 (le_of_lt hC1)
      _ = C1 * CB ^ 2 * x ^ 3 := by ring
  calc |G * x * (eps - x) + (eps * Real.exp u - 1 - G * eps) * x|
      ≤ |G * x * (eps - x)| + |(eps * Real.exp u - 1 - G * eps) * x| := abs_add_le _ _
    _ ≤ |G| * CE * x ^ 3 + C1 * CB ^ 2 * x ^ 3 := by linarith
    _ = (|G| * CE + C1 * CB ^ 2) * x ^ 3 := by ring

/-- The signed Jacobian in u-coordinates:

    J(u) = e^-u + 2 gamma e^-2u + O(e^-3u)

Composes jacobian_signed (J = eps + G eps^2 + O(eps^3)) with eps_of_u_signed
(eps = x + G x^2 + O(x^3), x = e^-u).  The 2G arises as G from each. -/
theorem jacobian_u_signed :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - Real.exp (-u)
        - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u)|
        ≤ C * Real.exp (-3 * u) := by
  obtain ⟨CJ, hCJ, rJ, hrJ, hJ⟩ := jacobian_signed
  obtain ⟨CS, hCS, US, hUS, hS⟩ := eps_of_u_signed
  obtain ⟨CE, hCE, UE, hUE, hE⟩ := eps_of_u_expansion
  obtain ⟨CB, hCB, UB, hUB, hBd⟩ := eps_of_u_bound
  set G := Real.eulerMascheroniConstant with hG
  -- eps(u) <= rJ for u large
  have hUr : ∃ U1 > 0, ∀ u : ℝ, U1 ≤ u → sOf u - 1 ≤ rJ := by
    refine ⟨max UB (Real.log (CB / rJ) + 1), by positivity, ?_⟩
    intro u hu
    have huB : UB ≤ u := le_trans (le_max_left _ _) hu
    have hlog : Real.log (CB / rJ) + 1 ≤ u := le_trans (le_max_right _ _) hu
    have hb := hBd u huB
    have hexp : CB * Real.exp (-u) ≤ rJ := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos u)]
      calc CB = rJ * (CB / rJ) := by field_simp
        _ ≤ rJ * Real.exp u := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hrJ)
            calc CB / rJ = Real.exp (Real.log (CB / rJ)) :=
                  (Real.exp_log (by positivity)).symm
              _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    linarith
  obtain ⟨U1, hU1, hr⟩ := hUr
  refine ⟨CJ * CB ^ 3 + CS + |G| * CE * (CB + 1), by positivity,
    max (max (max US UE) UB) U1, by positivity, ?_⟩
  intro u hu
  have huS : US ≤ u :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hu
  have huE : UE ≤ u :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hu
  have huB : UB ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu1 : U1 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU1 hu1
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  set eps := sOf u - 1 with hepsdef
  set x := Real.exp (-u) with hxdef
  set J := (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)) with hJdef
  have hxpos : 0 < x := Real.exp_pos _
  have heps0 : 0 < eps := by rw [hepsdef]; linarith
  have hx2 : Real.exp (-2 * u) = x ^ 2 := by
    rw [hxdef, ← Real.exp_nat_mul]; ring_nf
  have hx3 : Real.exp (-3 * u) = x ^ 3 := by
    rw [hxdef, ← Real.exp_nat_mul]; ring_nf
  have hjb : |J - eps - G * eps ^ 2| ≤ CJ * eps ^ 3 := hJ (sOf u) hs1 (hr u hu1)
  have hsb : |eps - x - G * x ^ 2| ≤ CS * x ^ 3 := by
    have h := hS u huS
    rw [hx2, hx3] at h
    exact h
  have heb : |eps - x| ≤ CE * x ^ 2 := by
    have h := hE u huE
    rw [hx2] at h
    exact h
  have hbb : eps ≤ CB * x := hBd u huB
  rw [hx2, hx3]
  have hid : J - x - 2 * G * x ^ 2
      = (J - eps - G * eps ^ 2) + (eps - x - G * x ^ 2) + G * (eps ^ 2 - x ^ 2) := by
    ring
  rw [hid]
  -- term 3: |G (eps^2 - x^2)| = |G| |eps - x| |eps + x|
  have hsum : |eps + x| ≤ (CB + 1) * x := by
    rw [abs_of_pos (by linarith)]
    linarith [hbb]
  have t3 : |G * (eps ^ 2 - x ^ 2)| ≤ |G| * CE * (CB + 1) * x ^ 3 := by
    have hfac : eps ^ 2 - x ^ 2 = (eps - x) * (eps + x) := by ring
    rw [hfac, abs_mul, abs_mul]
    calc |G| * (|eps - x| * |eps + x|) ≤ |G| * ((CE * x ^ 2) * ((CB + 1) * x)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg G)
          exact mul_le_mul heb hsum (abs_nonneg _) (by positivity)
      _ = |G| * CE * (CB + 1) * x ^ 3 := by ring
  -- term 1: |J - eps - G eps^2| <= CJ eps^3 <= CJ CB^3 x^3
  have t1 : |J - eps - G * eps ^ 2| ≤ CJ * CB ^ 3 * x ^ 3 := by
    have hcube : eps ^ 3 ≤ CB ^ 3 * x ^ 3 := by
      have h := pow_le_pow_left₀ (le_of_lt heps0) hbb 3
      calc eps ^ 3 ≤ (CB * x) ^ 3 := h
        _ = CB ^ 3 * x ^ 3 := by ring
    calc |J - eps - G * eps ^ 2| ≤ CJ * eps ^ 3 := hjb
      _ ≤ CJ * (CB ^ 3 * x ^ 3) := mul_le_mul_of_nonneg_left hcube (le_of_lt hCJ)
      _ = CJ * CB ^ 3 * x ^ 3 := by ring
  calc |(J - eps - G * eps ^ 2) + (eps - x - G * x ^ 2) + G * (eps ^ 2 - x ^ 2)|
      ≤ |(J - eps - G * eps ^ 2) + (eps - x - G * x ^ 2)| + |G * (eps ^ 2 - x ^ 2)| :=
        abs_add_le _ _
    _ ≤ (|J - eps - G * eps ^ 2| + |eps - x - G * x ^ 2|) + |G * (eps ^ 2 - x ^ 2)| := by
        linarith [abs_add_le (J - eps - G * eps ^ 2) (eps - x - G * x ^ 2)]
    _ ≤ CJ * CB ^ 3 * x ^ 3 + CS * x ^ 3 + |G| * CE * (CB + 1) * x ^ 3 := by
        linarith [t1, hsb, t3]
    _ = (CJ * CB ^ 3 + CS + |G| * CE * (CB + 1)) * x ^ 3 := by ring

/-! ### Option 2: toward discharging `OddNumericalFacts.remainder`

Step D needs `sum_j bHatOdd j * 2^j = 2 dConst (log 2 - Sodd)`, i.e.
`d_s H(s,2)` at `s = 1`.  Logarithmic differentiation of

    H(s,2) = (1 - 2^-s)^2 prod_{p>=3} (1 - 2 p^-s)^-1 (1 - p^-s)^2

gives, at s = 1,

    d_s log H(1,2) = 2 log 2 - 2 sum_{p>=3} log p/((p-1)(p-2)) = 2(log 2 - S)

and hence d_s H(1,2) = H(1,2) (2 log 2 - 2S) = 2 d (log 2 - S), the source of
the `log 2 - S` in beta.  The p = 2 prefactor supplies the log 2; the odd
primes supply the -S. -/

/-- The p = 2 prefactor's logarithmic derivative at s = 1 is 2 log 2. -/
theorem prefactor_logderiv :
    HasDerivAt (fun s : ℝ => 2 * Real.log (1 - (2:ℝ) ^ (-s))) (2 * Real.log 2) 1 := by
  have hb : (0:ℝ) < 2 := by norm_num
  -- d/ds (2^-s) = -log 2 * 2^-s
  have hpow : HasDerivAt (fun s : ℝ => (2:ℝ) ^ (-s))
      (-(Real.log 2 * (2:ℝ) ^ (-(1:ℝ)))) 1 := by
    have h := HasDerivAt.const_rpow hb (hasDerivAt_neg (1:ℝ))
    simpa using h
  have hinner : HasDerivAt (fun s : ℝ => 1 - (2:ℝ) ^ (-s))
      (Real.log 2 * (2:ℝ) ^ (-(1:ℝ))) 1 := by
    simpa using hpow.const_sub 1
  have hne : (1:ℝ) - (2:ℝ) ^ (-(1:ℝ)) ≠ 0 := by
    rw [Real.rpow_neg_one]
    norm_num
  have hlog := (hinner.log hne).const_mul 2
  have hval : 2 * (Real.log 2 * (2:ℝ) ^ (-(1:ℝ)) / (1 - (2:ℝ) ^ (-(1:ℝ))))
      = 2 * Real.log 2 := by
    rw [Real.rpow_neg_one]
    norm_num
  rw [← hval]
  exact hlog

/-- Each odd prime's logarithmic-derivative contribution at s = 1.

d/ds [ -log(1 - 2 p^-s) + 2 log(1 - p^-s) ] at s = 1
  = -2 log p/(p-2) + 2 log p/(p-1)
  = -2 log p/((p-1)(p-2)) -/
theorem prime_logderiv (p : ℕ) (hp : 3 ≤ p) :
    HasDerivAt (fun s : ℝ =>
        -Real.log (1 - 2 * (p:ℝ) ^ (-s)) + 2 * Real.log (1 - (p:ℝ) ^ (-s)))
      (-2 * Real.log p / (((p:ℝ) - 1) * ((p:ℝ) - 2))) 1 := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  have hp1 : (p:ℝ) ^ (-(1:ℝ)) = 1 / (p:ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  have hpow : HasDerivAt (fun s : ℝ => (p:ℝ) ^ (-s))
      (-(Real.log p * (p:ℝ) ^ (-(1:ℝ)))) 1 := by
    have h := HasDerivAt.const_rpow hp0 (hasDerivAt_neg (1:ℝ))
    simpa using h
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  -- first log: 1 - 2 p^-s
  have hin1 : HasDerivAt (fun s : ℝ => 1 - 2 * (p:ℝ) ^ (-s))
      (2 * (Real.log p * (p:ℝ) ^ (-(1:ℝ)))) 1 := by
    simpa using (hpow.const_mul (2:ℝ)).const_sub 1
  have hne1 : (1:ℝ) - 2 * (p:ℝ) ^ (-(1:ℝ)) ≠ 0 := by
    rw [hp1]
    have : (2:ℝ) / (p:ℝ) < 1 := by
      rw [div_lt_one hp0]; linarith
    intro hc
    rw [mul_one_div] at hc
    linarith [hc]
  -- second log: 1 - p^-s
  have hin2 : HasDerivAt (fun s : ℝ => 1 - (p:ℝ) ^ (-s))
      (Real.log p * (p:ℝ) ^ (-(1:ℝ))) 1 := by
    simpa using hpow.const_sub 1
  have hne2 : (1:ℝ) - (p:ℝ) ^ (-(1:ℝ)) ≠ 0 := by
    rw [hp1]
    have : (1:ℝ) / (p:ℝ) < 1 := by
      rw [div_lt_one hp0]; linarith
    intro hc
    linarith [hc]
  have hL1 := (hin1.log hne1).neg
  have hL2 := (hin2.log hne2).const_mul 2
  have hsum := hL1.add hL2
  have hval : -(2 * (Real.log p * (p:ℝ) ^ (-(1:ℝ))) / (1 - 2 * (p:ℝ) ^ (-(1:ℝ))))
      + 2 * (Real.log p * (p:ℝ) ^ (-(1:ℝ)) / (1 - (p:ℝ) ^ (-(1:ℝ))))
      = -2 * Real.log p / (((p:ℝ) - 1) * ((p:ℝ) - 2)) := by
    rw [hp1]
    have h1 : (p:ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p:ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hval]
  exact hsum

/-- The odd-prime part of log H(s,2), as a sum over p >= 3. -/
noncomputable def logHodd2 (s : ℝ) : ℝ :=
  ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
    (-Real.log (1 - 2 * ((p:ℕ):ℝ) ^ (-s)) + 2 * Real.log (1 - ((p:ℕ):ℝ) ^ (-s)))

/-- log n * n^-t is summable over any subtype of the naturals, for t > 1. -/
theorem log_rpow_summable_subtype (t : ℝ) (ht : 1 < t) (S : Set ℕ) :
    Summable (fun n : S => Real.log ((n:ℕ):ℝ) * (((n:ℕ):ℝ)) ^ (-t)) := by
  have hbase : Summable (fun n : ℕ => Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-t)) :=
    log_rpow_summable t ht
  have hshift : Summable (fun n : ℕ => Real.log ((n:ℝ)) * ((n:ℝ)) ^ (-t)) := by
    apply (summable_nat_add_iff 1).mp
    apply hbase.congr
    intro n
    push_cast
    ring_nf
  exact hshift.subtype S


/-- For p >= 3 and s > 3/4, p^s > 2.  The key point is 3^(3/4) > 2,
i.e. 3^3 = 27 > 16 = 2^4. -/
theorem three_rpow_gt_two' (q : ℝ) (hq : 3 ≤ q) (s : ℝ) (hs : 3/4 < s) :
    (9:ℝ)/4 < q ^ s := by
  have hq0 : (0:ℝ) < q := by linarith
  have h34 : (9:ℝ)/4 < (3:ℝ) ^ ((3:ℝ)/4) := by
    have hpos : (0:ℝ) < (3:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
    have hpow : ((3:ℝ) ^ ((3:ℝ)/4)) ^ (4:ℕ) = 27 := by
      rw [← Real.rpow_natCast ((3:ℝ) ^ ((3:ℝ)/4)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra hcon
    push_neg at hcon
    have h16 : ((3:ℝ) ^ ((3:ℝ)/4)) ^ (4:ℕ) ≤ ((9:ℝ)/4) ^ (4:ℕ) :=
      pow_le_pow_left₀ (le_of_lt hpos) hcon 4
    rw [hpow] at h16
    norm_num at h16
  calc (9:ℝ)/4 < (3:ℝ) ^ ((3:ℝ)/4) := h34
    _ ≤ q ^ ((3:ℝ)/4) := by
        apply Real.rpow_le_rpow (by norm_num) hq (by norm_num)
    _ ≤ q ^ s := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith) (le_of_lt hs)


/-- The differentiated series is summable for s > 3/4.

|f_p'(s)| = 2 log p/((p^s - 1)(p^s - 2)) ~ 2 log p / p^(2s), summable for
2s > 1.  Unlike the zeta series, s = 1 is INTERIOR here: the p >= 3 Euler
factors have no pole at s = 1. -/
theorem logHodd2_deriv_summable (s : ℝ) (hs : 3/4 < s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      2 * Real.log ((p:ℕ):ℝ) / ((((p:ℕ):ℝ) ^ s - 1) * (((p:ℕ):ℝ) ^ s - 2))) := by
  have hcomp := log_rpow_summable_subtype (2*s) (by linarith)
    {p : ℕ | p.Prime ∧ 3 ≤ p}
  apply Summable.of_nonneg_of_le _ _ (hcomp.mul_left 33)
  · intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hqs' : (9:ℝ)/4 < ((q:ℕ):ℝ) ^ s := three_rpow_gt_two' _ hq3 s hs
    have hqs : (2:ℝ) < ((q:ℕ):ℝ) ^ s := by linarith
    have hlog : (0:ℝ) ≤ Real.log ((q:ℕ):ℝ) := by
      apply Real.log_nonneg; linarith
    have h1 : (0:ℝ) < ((q:ℕ):ℝ) ^ s - 1 := by linarith
    have h2 : (0:ℝ) < ((q:ℕ):ℝ) ^ s - 2 := by linarith
    positivity
  · intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hqs : (9:ℝ)/4 < ((q:ℕ):ℝ) ^ s := three_rpow_gt_two' _ hq3 s hs
    set P := ((q:ℕ):ℝ) ^ s with hP
    have hP0 : (0:ℝ) < P := by linarith
    have hlog : (0:ℝ) ≤ Real.log ((q:ℕ):ℝ) := by
      apply Real.log_nonneg; linarith
    have h1 : (5:ℝ)/9 * P ≤ P - 1 := by nlinarith [hqs]
    have h2 : (1:ℝ)/9 * P ≤ P - 2 := by nlinarith [hqs]
    have hprod : (5:ℝ)/81 * P ^ 2 ≤ (P - 1) * (P - 2) := by nlinarith [h1, h2, hP0]
    have hP2 : P ^ 2 = ((q:ℕ):ℝ) ^ (2*s) := by
      rw [hP, ← Real.rpow_natCast (((q:ℕ):ℝ) ^ s) 2, ← Real.rpow_mul (by positivity)]
      ring_nf
    rw [div_le_iff₀ (by nlinarith [hprod, hP0])]
    have hrp : ((q:ℕ):ℝ) ^ (-(2*s)) = 1 / ((q:ℕ):ℝ) ^ (2*s) := by
      rw [Real.rpow_neg (by positivity), one_div]
    rw [hrp, ← hP2]
    have hPpow : (0:ℝ) < P ^ 2 := by positivity
    have hkey : (5:ℝ)/81 ≤ (P - 1) * (P - 2) / P ^ 2 := by
      rw [le_div_iff₀ hPpow]
      linarith [hprod]
    have hstep : 2 * Real.log ((q:ℕ):ℝ)
        ≤ 33 * Real.log ((q:ℕ):ℝ) * ((5:ℝ)/81) := by
      nlinarith [hlog]
    calc 2 * Real.log ((q:ℕ):ℝ) ≤ 33 * Real.log ((q:ℕ):ℝ) * ((5:ℝ)/81) := hstep
      _ ≤ 33 * (Real.log ((q:ℕ):ℝ) * (1 / P ^ 2)) * ((P - 1) * (P - 2)) := by
          have hrw : 33 * (Real.log ((q:ℕ):ℝ) * (1 / P ^ 2)) * ((P - 1) * (P - 2))
              = 33 * Real.log ((q:ℕ):ℝ) * ((P - 1) * (P - 2) / P ^ 2) := by
            field_simp
          rw [hrw]
          apply mul_le_mul_of_nonneg_left hkey (by positivity)

/-- The undifferentiated series converges: the p^-s terms cancel at first
order, leaving O(p^-2s).  This is the same cancellation that makes H
analytic where the bare Euler factors are not. -/
theorem logHodd2_summable (s : ℝ) (hs : 3/4 < s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      -Real.log (1 - 2 * ((p:ℕ):ℝ) ^ (-s)) + 2 * Real.log (1 - ((p:ℕ):ℝ) ^ (-s))) := by
  have hbase : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(2*s))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcomp : Summable (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      9 * (((q:ℕ):ℝ)) ^ (-(2*s))) := (hbase.subtype _).mul_left 9
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hqs : (9:ℝ)/4 < ((q:ℕ):ℝ) ^ s := three_rpow_gt_two' _ hq3 s hs
    set x := ((q:ℕ):ℝ) ^ (-s) with hx
    have hxpos : 0 < x := Real.rpow_pos_of_pos (by linarith) _
    have hxval : x = 1 / ((q:ℕ):ℝ) ^ s := by
      rw [hx, Real.rpow_neg (by linarith), one_div]
    have hxlt : x < 4/9 := by
      rw [hxval, div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2x : (0:ℝ) < 1 - 2 * x := by linarith
    have h1x : (0:ℝ) < 1 - x := by linarith
    -- -log(1-2x) + 2log(1-x) = log((1-x)^2/(1-2x)) >= 0
    have hid : -Real.log (1 - 2*x) + 2 * Real.log (1 - x)
        = Real.log ((1-x)^2 / (1-2*x)) := by
      rw [Real.log_div (by positivity) (ne_of_gt h2x), Real.log_pow]
      push_cast
      ring
    rw [hid]
    apply Real.log_nonneg
    rw [le_div_iff₀ h2x]
    nlinarith [hxpos]
  · intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hqs : (9:ℝ)/4 < ((q:ℕ):ℝ) ^ s := three_rpow_gt_two' _ hq3 s hs
    set x := ((q:ℕ):ℝ) ^ (-s) with hx
    have hxpos : 0 < x := Real.rpow_pos_of_pos (by linarith) _
    have hxval : x = 1 / ((q:ℕ):ℝ) ^ s := by
      rw [hx, Real.rpow_neg (by linarith), one_div]
    have hxlt : x < 4/9 := by
      rw [hxval, div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h2x : (1:ℝ)/9 < 1 - 2 * x := by linarith
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hid : -Real.log (1 - 2*x) + 2 * Real.log (1 - x)
        = Real.log (1 + x^2 / (1 - 2*x)) := by
      have hne : (1:ℝ) - 2*x ≠ 0 := by linarith
      have hrw : (1:ℝ) + x^2/(1-2*x) = (1-x)^2/(1-2*x) := by
        rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
        ring
      rw [hrw]
      rw [Real.log_div (by positivity) (by linarith), Real.log_pow]
      push_cast
      ring
    have hsq : x ^ 2 = ((q:ℕ):ℝ) ^ (-(2*s)) := by
      rw [hx, ← Real.rpow_natCast (((q:ℕ):ℝ) ^ (-s)) 2, ← Real.rpow_mul (by linarith)]
      ring_nf
    rw [hid, ← hsq]
    calc Real.log (1 + x^2/(1-2*x)) ≤ x^2/(1-2*x) := by
          have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + x^2/(1-2*x))
          linarith
      _ ≤ 9 * x^2 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [hxpos, h2x]

/-- The per-prime derivative at general s, not just s = 1.  At s = 1 the
value collapses to -2 log p/((p-1)(p-2)), which is prime_logderiv. -/
theorem prime_logderiv_gen (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 3/4 < s) :
    HasDerivAt (fun t : ℝ =>
        -Real.log (1 - 2 * (p:ℝ) ^ (-t)) + 2 * Real.log (1 - (p:ℝ) ^ (-t)))
      (-2 * Real.log p * (p:ℝ) ^ (-s) / (1 - 2 * (p:ℝ) ^ (-s))
        + 2 * Real.log p * (p:ℝ) ^ (-s) / (1 - (p:ℝ) ^ (-s))) s := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hqs : (9:ℝ)/4 < (p:ℝ) ^ s := three_rpow_gt_two' _ hp3 s hs
  have hxpos : 0 < (p:ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hxval : (p:ℝ) ^ (-s) = 1 / (p:ℝ) ^ s := by
    rw [Real.rpow_neg (le_of_lt hp0), one_div]
  have hxlt : (p:ℝ) ^ (-s) < 4/9 := by
    rw [hxval, div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2x : (0:ℝ) < 1 - 2 * (p:ℝ) ^ (-s) := by linarith
  have h1x : (0:ℝ) < 1 - (p:ℝ) ^ (-s) := by linarith
  have hpow : HasDerivAt (fun t : ℝ => (p:ℝ) ^ (-t))
      (-(Real.log p * (p:ℝ) ^ (-s))) s := by
    have h := HasDerivAt.const_rpow hp0 (hasDerivAt_neg s)
    simpa using h
  have hin1 : HasDerivAt (fun t : ℝ => 1 - 2 * (p:ℝ) ^ (-t))
      (2 * (Real.log p * (p:ℝ) ^ (-s))) s := by
    simpa using (hpow.const_mul (2:ℝ)).const_sub 1
  have hin2 : HasDerivAt (fun t : ℝ => 1 - (p:ℝ) ^ (-t))
      (Real.log p * (p:ℝ) ^ (-s)) s := by
    simpa using hpow.const_sub 1
  have hL1 := (hin1.log (ne_of_gt h2x)).neg
  have hL2 := (hin2.log (ne_of_gt h1x)).const_mul 2
  have hsum := hL1.add hL2
  have hval : -(2 * (Real.log p * (p:ℝ) ^ (-s)) / (1 - 2 * (p:ℝ) ^ (-s)))
      + 2 * (Real.log p * (p:ℝ) ^ (-s) / (1 - (p:ℝ) ^ (-s)))
      = -2 * Real.log p * (p:ℝ) ^ (-s) / (1 - 2 * (p:ℝ) ^ (-s))
        + 2 * Real.log p * (p:ℝ) ^ (-s) / (1 - (p:ℝ) ^ (-s)) := by
    field_simp
  rw [← hval]
  exact hsum

/-- The two forms of the per-prime derivative agree for every s, not just at
s = 1: multiplying through by p^(2s),

    -2 L x/(1-2x) + 2 L x/(1-x)  =  -2 L/((P-1)(P-2)),   x = 1/P, P = p^s.

This is what connects prime_logderiv_gen's conclusion to the majorant used in
logHodd2_deriv_summable. -/
theorem prime_logderiv_forms_eq (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 3/4 < s) :
    -2 * Real.log p * (p:ℝ) ^ (-s) / (1 - 2 * (p:ℝ) ^ (-s))
      + 2 * Real.log p * (p:ℝ) ^ (-s) / (1 - (p:ℝ) ^ (-s))
      = -2 * Real.log p / (((p:ℝ) ^ s - 1) * ((p:ℝ) ^ s - 2)) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hP : (9:ℝ)/4 < (p:ℝ) ^ s := three_rpow_gt_two' _ hp3 s hs
  have hPpos : (0:ℝ) < (p:ℝ) ^ s := by linarith
  have hxval : (p:ℝ) ^ (-s) = 1 / (p:ℝ) ^ s := by
    rw [Real.rpow_neg (le_of_lt hp0), one_div]
  have h1 : (p:ℝ) ^ s - 1 ≠ 0 := by linarith
  have h2 : (p:ℝ) ^ s - 2 ≠ 0 := by linarith
  have hPne : (p:ℝ) ^ s ≠ 0 := ne_of_gt hPpos
  rw [hxval]
  field_simp
  ring

/-- The summed derivative: d/ds logHodd2 at s in (3/4, 2) is the sum of the
per-prime contributions. -/
theorem logHodd2_hasDerivAt (s : ℝ) (hs : 3/4 < s) (hs2 : s < 2) :
    HasDerivAt logHodd2
      (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-2 * Real.log ((p:ℕ):ℝ) * ((p:ℕ):ℝ) ^ (-s)
            / (1 - 2 * ((p:ℕ):ℝ) ^ (-s))
          + 2 * Real.log ((p:ℕ):ℝ) * ((p:ℕ):ℝ) ^ (-s)
            / (1 - ((p:ℕ):ℝ) ^ (-s)))) s := by
  have hterm : ∀ (q : {p : ℕ // p.Prime ∧ 3 ≤ p}) (t : ℝ), 3/4 < t →
      HasDerivAt (fun r : ℝ =>
          -Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-r)) + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-r)))
        (-2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t) / (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
          + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t) / (1 - ((q:ℕ):ℝ) ^ (-t))) t := by
    intro q t ht
    exact prime_logderiv_gen (q:ℕ) q.2.2 t ht
  have hfun : logHodd2 = fun t : ℝ => ∑' q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-t))) := by
    funext t
    rfl
  rw [hfun]
  apply hasDerivAt_of_tendstoLocallyUniformlyOn (s := Set.Ioo (3/4 : ℝ) 2)
    (l := Filter.atTop) isOpen_Ioo
    (g := fun t : ℝ => ∑' q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-t))))
    (g' := fun t : ℝ => ∑' q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t)
          / (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
        + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t)
          / (1 - ((q:ℕ):ℝ) ^ (-t))))
    (f := fun N : Finset {p : ℕ // p.Prime ∧ 3 ≤ p} => fun t : ℝ =>
      ∑ q ∈ N, (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-t))))
    (f' := fun N : Finset {p : ℕ // p.Prime ∧ 3 ≤ p} => fun t : ℝ =>
      ∑ q ∈ N, (-2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t)
          / (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
        + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t)
          / (1 - ((q:ℕ):ℝ) ^ (-t))))
  · -- (a) local uniform convergence of the differentiated partial sums
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo]
    intro K hKsub hKcomp
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · subst hKe; simp [tendstoUniformlyOn_empty]
    · obtain ⟨c, hcK, hcmin⟩ := hKcomp.exists_isMinOn hKne continuousOn_id
      have hc : (3/4 : ℝ) < c := (hKsub hcK).1
      apply tendstoUniformlyOn_tsum
        (u := fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
          2 * Real.log ((q:ℕ):ℝ) / ((((q:ℕ):ℝ) ^ c - 1) * ((((q:ℕ):ℝ) ^ c - 2))))
        (logHodd2_deriv_summable c hc)
      intro q x hx
      have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
        have := q.2.2
        exact_mod_cast this
      have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
      have hxc : c ≤ x := hcmin hx
      have hx34 : (3/4:ℝ) < x := lt_of_lt_of_le hc hxc
      have hPc : (9:ℝ)/4 < ((q:ℕ):ℝ) ^ c := three_rpow_gt_two' _ hq3 c hc
      have hPx : (9:ℝ)/4 < ((q:ℕ):ℝ) ^ x := three_rpow_gt_two' _ hq3 x hx34
      have hmono : ((q:ℕ):ℝ) ^ c ≤ ((q:ℕ):ℝ) ^ x :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hxc
      have hlog : (0:ℝ) ≤ Real.log ((q:ℕ):ℝ) := by
        apply Real.log_nonneg; linarith
      rw [prime_logderiv_forms_eq (q:ℕ) q.2.2 x hx34]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by nlinarith [hPx] :
        (0:ℝ) ≤ (((q:ℕ):ℝ) ^ x - 1) * (((q:ℕ):ℝ) ^ x - 2))]
      have habs : |-2 * Real.log ((q:ℕ):ℝ)| = 2 * Real.log ((q:ℕ):ℝ) := by
        rw [abs_of_nonpos (by nlinarith [hlog])]
        ring
      rw [habs]
      apply div_le_div_of_nonneg_left (by linarith) (by nlinarith [hPc])
      nlinarith [hmono, hPc, hPx]
  · -- (b) each partial sum has the stated derivative
    filter_upwards with N t ht
    have ht34 : (3/4 : ℝ) < t := ht.1
    have h := HasDerivAt.sum (u := N)
      (A := fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} => fun r : ℝ =>
        -Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-r)) + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-r)))
      (A' := fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        -2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t) / (1 - 2 * ((q:ℕ):ℝ) ^ (-t))
          + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-t) / (1 - ((q:ℕ):ℝ) ^ (-t)))
      (fun q _ => hterm q t ht34)
    have hfn : (fun r : ℝ => ∑ q ∈ N, (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-r))
          + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-r))))
        = ∑ q ∈ N, (fun r : ℝ =>
            -Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-r))
              + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-r))) := by
      funext r
      rw [Finset.sum_apply]
    rw [hfn]
    exact h
  · -- (c) pointwise convergence of the partial sums
    intro t ht
    have ht34 : (3/4 : ℝ) < t := ht.1
    exact (logHodd2_summable t ht34).hasSum
  · exact ⟨hs, hs2⟩

/-- At s = 1 the general-s summand collapses to prime_logderiv's form:
p^-1/(1-2p^-1) = 1/(p-2), p^-1/(1-p^-1) = 1/(p-1). -/
theorem prime_logderiv_at_one (p : ℕ) (hp : 3 ≤ p) :
    -2 * Real.log p * (p:ℝ) ^ (-(1:ℝ)) / (1 - 2 * (p:ℝ) ^ (-(1:ℝ)))
      + 2 * Real.log p * (p:ℝ) ^ (-(1:ℝ)) / (1 - (p:ℝ) ^ (-(1:ℝ)))
      = -2 * Real.log p / (((p:ℝ) - 1) * ((p:ℝ) - 2)) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have h1 : (p:ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p:ℝ) - 2 ≠ 0 := by linarith
  have hpne : (p:ℝ) ≠ 0 := by linarith
  rw [Real.rpow_neg_one]
  field_simp
  ring

/-- At s = 1 the summed derivative is -2 Sodd: each summand collapses by
prime_logderiv_at_one to -2 log p/((p-1)(p-2)). -/
theorem logHodd2_deriv_at_one :
    (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-2 * Real.log ((p:ℕ):ℝ) * ((p:ℕ):ℝ) ^ (-(1:ℝ))
          / (1 - 2 * ((p:ℕ):ℝ) ^ (-(1:ℝ)))
        + 2 * Real.log ((p:ℕ):ℝ) * ((p:ℕ):ℝ) ^ (-(1:ℝ))
          / (1 - ((p:ℕ):ℝ) ^ (-(1:ℝ)))))
      = -2 * Sodd := by
  have hcongr : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-(1:ℝ))
          / (1 - 2 * ((q:ℕ):ℝ) ^ (-(1:ℝ)))
        + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-(1:ℝ))
          / (1 - ((q:ℕ):ℝ) ^ (-(1:ℝ))))
      = -2 * (Real.log ((q:ℕ):ℝ) / ((((q:ℕ):ℝ) - 1) * ((((q:ℕ):ℝ)) - 2))) := by
    intro q
    rw [prime_logderiv_at_one (q:ℕ) q.2.2]
    ring
  rw [tsum_congr hcongr, tsum_mul_left]
  unfold Sodd
  rfl

/-- STEP 2: d_s log H(1,2) = 2 log 2 - 2 Sodd. -/
theorem logH_deriv_at_one :
    HasDerivAt (fun s : ℝ => 2 * Real.log (1 - (2:ℝ) ^ (-s)) + logHodd2 s)
      (2 * Real.log 2 - 2 * Sodd) 1 := by
  have h1 := prefactor_logderiv
  have h2 := logHodd2_hasDerivAt 1 (by norm_num) (by norm_num)
  rw [logHodd2_deriv_at_one] at h2
  have h := h1.add h2
  have hval : 2 * Real.log 2 + -2 * Sodd = 2 * Real.log 2 - 2 * Sodd := by ring
  rw [← hval]
  exact h

/-- Real analogue of `hasProd_exp_of_hasSum`: exp carries a HasSum to a
HasProd.  Mathlib has neither direction for the reals. -/
theorem hasProd_rexp_of_hasSum {ι : Type*} {g : ι → ℝ} {a : ℝ}
    (h : HasSum g a) :
    HasProd (fun i => Real.exp (g i)) (Real.exp a) := by
  have hcont : Filter.Tendsto Real.exp (nhds a) (nhds (Real.exp a)) :=
    (Real.continuous_exp.tendsto a)
  have hc := hcont.comp h
  apply hc.congr
  intro t
  simp only [Function.comp_apply]
  exact Real.exp_sum t g

/-- The real-valued H(s,2), as the exponential of its logarithm.

Working with exp of the log-sum rather than with the product itself avoids
needing log of an infinite product: the derivative is then HasDerivAt.exp
applied to logH_deriv_at_one. -/
noncomputable def HoddR2 (s : ℝ) : ℝ :=
  Real.exp (2 * Real.log (1 - (2:ℝ) ^ (-s)) + logHodd2 s)

/-- STEP 3: d_s H(1,2) = H(1,2) * (2 log 2 - 2 Sodd), i.e. 2d(log 2 - Sodd)
once H(1,2) = d is substituted. -/
theorem HoddR2_hasDerivAt_one :
    HasDerivAt HoddR2 (HoddR2 1 * (2 * Real.log 2 - 2 * Sodd)) 1 := by
  have h := logH_deriv_at_one.exp
  unfold HoddR2
  convert h using 1

/-- H(1,2) = d: the exponential form agrees with the product at s = 1. -/
theorem HoddR2_at_one : HoddR2 1 = dConst := by
  unfold HoddR2
  -- the prefactor: 2 log(1 - 2^-1) = -2 log 2, so exp of it is 1/4
  have hpre : 2 * Real.log (1 - (2:ℝ) ^ (-(1:ℝ))) = -(2 * Real.log 2) := by
    rw [Real.rpow_neg_one]
    norm_num
    rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [hpre, Real.exp_add, Real.exp_neg]
  have hquarter : (Real.exp (2 * Real.log 2))⁻¹ = 1/4 := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [hquarter]
  unfold dConst
  rw [dConst_prod_eq_subtype]
  congr 1
  -- each factor is positive
  have hpos : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (0:ℝ) < (1 - 2 / ((q:ℕ):ℝ))⁻¹ * (1 - 1 / ((q:ℕ):ℝ)) ^ 2 := by
    intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have h2 : (0:ℝ) < 1 - 2 / ((q:ℕ):ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    have h1 : (0:ℝ) < 1 - 1 / ((q:ℕ):ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    positivity
  -- the summands agree with the logs of the factors
  have hlogeq : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      Real.exp (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-(1:ℝ)))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-(1:ℝ))))
      = (1 - 2 / ((q:ℕ):ℝ))⁻¹ * (1 - 1 / ((q:ℕ):ℝ)) ^ 2 := by
    intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
    have h2 : (0:ℝ) < 1 - 2 / ((q:ℕ):ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    have h1 : (0:ℝ) < 1 - 1 / ((q:ℕ):ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    rw [Real.rpow_neg_one]
    rw [Real.exp_add, Real.exp_neg]
    rw [show (2:ℝ) * ((q:ℕ):ℝ)⁻¹ = 2 / ((q:ℕ):ℝ) by ring]
    rw [show ((q:ℕ):ℝ)⁻¹ = 1 / ((q:ℕ):ℝ) by ring]
    rw [Real.exp_log h2, two_mul, Real.exp_add, Real.exp_log h1]
    ring
  -- HasSum -> HasProd via exp
  have hsum : HasSum (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      -Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-(1:ℝ)))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-(1:ℝ)))) (logHodd2 1) :=
    (logHodd2_summable 1 (by norm_num)).hasSum
  have hprod := hasProd_rexp_of_hasSum hsum
  have hprod' : HasProd (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((q:ℕ):ℝ))⁻¹ * (1 - 1 / ((q:ℕ):ℝ)) ^ 2)
      (Real.exp (logHodd2 1)) := by
    have hfe : (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} => Real.exp
        (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-(1:ℝ)))
          + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-(1:ℝ)))))
        = fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
          (1 - 2 / ((q:ℕ):ℝ))⁻¹ * (1 - 1 / ((q:ℕ):ℝ)) ^ 2 := by
      funext q
      exact hlogeq q
    rw [hfe] at hprod
    exact hprod
  exact (hprod'.tprod_eq).symm

/-- STEP 3, in the form step D consumes:
    d_s H(1,2) = 2 d (log 2 - S). -/
theorem HoddR2_deriv_value :
    HasDerivAt HoddR2 (2 * dConst * (Real.log 2 - Sodd)) 1 := by
  have h := HoddR2_hasDerivAt_one
  rw [HoddR2_at_one] at h
  have hval : dConst * (2 * Real.log 2 - 2 * Sodd)
      = 2 * dConst * (Real.log 2 - Sodd) := by ring
  rw [← hval]
  exact h

/-! ### Step 4, part (i): continuity of L and L' near s = 1

L(s) = 2 log(1 - 2^-s) + logHodd2 s, so HoddR2 = exp o L and
deriv HoddR2 = HoddR2 * L'.  Both L and L' are continuous on (3/4, 2), where
s = 1 is interior -- the boundary difficulty is confined to hCoeff, which
lives on (1,2). -/

/-- L' as an explicit function: the prefactor term plus the prime sum. -/
noncomputable def LprimeOdd (s : ℝ) : ℝ :=
  2 * ((2:ℝ) ^ (-s) * Real.log 2 / (1 - (2:ℝ) ^ (-s)))
    + ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-2 * Real.log ((p:ℕ):ℝ) / ((((p:ℕ):ℝ) ^ s - 1) * (((p:ℕ):ℝ) ^ s - 2)))

/-- logHodd2 is continuous on (3/4, 2): the M-test again, with the
undifferentiated series. -/
theorem logHodd2_continuousOn :
    ContinuousOn logHodd2 (Set.Ioo (3/4 : ℝ) 2) := by
  intro s0 hs0
  have hs034 : (3/4:ℝ) < s0 := hs0.1
  set d := (s0 - 3/4) / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hc : (3/4:ℝ) < 3/4 + d := by linarith
  have hOn : ContinuousOn logHodd2 (Set.Ici (3/4 + d)) := by
    unfold logHodd2
    apply continuousOn_tsum
      (u := fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        9 * (((q:ℕ):ℝ)) ^ (-(2*(3/4 + d))))
      _ (((Real.summable_nat_rpow.mpr (by linarith :
        (-(2*(3/4 + d)) : ℝ) < -1)).subtype _).mul_left 9)
    · intro q x hx
      have hxle : (3:ℝ)/4 + d ≤ x := hx
      have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
        have := q.2.2
        exact_mod_cast this
      have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
      have hx34 : (3:ℝ)/4 < x := by linarith
      set y := ((q:ℕ):ℝ) ^ (-x) with hy
      have hypos : 0 < y := Real.rpow_pos_of_pos hq0 _
      have hqs := three_rpow_gt_two' _ hq3 x hx34
      have hyval : y = 1 / ((q:ℕ):ℝ) ^ x := by
        rw [hy, Real.rpow_neg (le_of_lt hq0), one_div]
      have hylt : y < 4/9 := by
        rw [hyval, div_lt_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have h2y : (1:ℝ)/9 < 1 - 2 * y := by linarith
      have h1y : (0:ℝ) < 1 - y := by linarith
      -- |g(y)| <= 9 y^2, exactly as in logHodd2_summable
      have hid : -Real.log (1 - 2*y) + 2 * Real.log (1 - y)
          = Real.log (1 + y^2 / (1 - 2*y)) := by
        have hne : (1:ℝ) - 2*y ≠ 0 := by linarith
        have hrw : (1:ℝ) + y^2/(1-2*y) = (1-y)^2/(1-2*y) := by
          rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
          ring
        rw [hrw, Real.log_div (by positivity) (by linarith), Real.log_pow]
        push_cast
        ring
      rw [hid, Real.norm_eq_abs, abs_of_nonneg]
      · have hle : Real.log (1 + y^2/(1-2*y)) ≤ 9 * y^2 := by
          calc Real.log (1 + y^2/(1-2*y)) ≤ y^2/(1-2*y) := by
                have := Real.log_le_sub_one_of_pos
                  (by positivity : (0:ℝ) < 1 + y^2/(1-2*y))
                linarith
            _ ≤ 9 * y^2 := by
                rw [div_le_iff₀ (by linarith)]
                nlinarith [hypos, h2y]
        have hy2 : y^2 = ((q:ℕ):ℝ) ^ (-(2*x)) := by
          rw [hy, ← Real.rpow_natCast (((q:ℕ):ℝ) ^ (-x)) 2,
            ← Real.rpow_mul (le_of_lt hq0)]
          ring_nf
        have hmono : ((q:ℕ):ℝ) ^ (-(2*x)) ≤ ((q:ℕ):ℝ) ^ (-(2*(3/4 + d))) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        calc Real.log (1 + y^2/(1-2*y)) ≤ 9 * y^2 := hle
          _ = 9 * ((q:ℕ):ℝ) ^ (-(2*x)) := by rw [hy2]
          _ ≤ 9 * ((q:ℕ):ℝ) ^ (-(2*(3/4 + d))) := by linarith
      · apply Real.log_nonneg
        have : (0:ℝ) ≤ y^2/(1-2*y) := by positivity
        linarith
    · intro q
      have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
        have := q.2.2
        exact_mod_cast this
      have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
      apply ContinuousOn.add
      · apply ContinuousOn.neg
        apply ContinuousOn.log
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul continuousOn_const
          apply Continuous.continuousOn
          exact (Real.continuous_const_rpow (ne_of_gt hq0)).comp continuous_neg
        · intro x hx
          have hxle : (3:ℝ)/4 + d ≤ x := hx
          have hqs := three_rpow_gt_two' _ hq3 x (by linarith)
          have hxv : ((q:ℕ):ℝ) ^ (-x) = 1 / ((q:ℕ):ℝ) ^ x := by
            rw [Real.rpow_neg (le_of_lt hq0), one_div]
          rw [hxv]
          intro hcon
          rw [sub_eq_zero] at hcon
          rw [eq_comm, mul_one_div, div_eq_one_iff_eq (by linarith)] at hcon
          linarith
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.log
        · apply ContinuousOn.sub continuousOn_const
          apply Continuous.continuousOn
          exact (Real.continuous_const_rpow (ne_of_gt hq0)).comp continuous_neg
        · intro x hx
          have hxle : (3:ℝ)/4 + d ≤ x := hx
          have hqs := three_rpow_gt_two' _ hq3 x (by linarith)
          have hxv : ((q:ℕ):ℝ) ^ (-x) = 1 / ((q:ℕ):ℝ) ^ x := by
            rw [Real.rpow_neg (le_of_lt hq0), one_div]
          rw [hxv]
          intro hcon
          rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq (by linarith)] at hcon
          linarith
  apply (hOn.continuousAt _).continuousWithinAt
  apply Ici_mem_nhds
  rw [hd]; linarith

theorem LprimeOdd_continuousOn :
    ContinuousOn LprimeOdd (Set.Ioo (3/4 : ℝ) 2) := by
  intro s0 hs0
  have hs034 : (3/4:ℝ) < s0 := hs0.1
  set d := (s0 - 3/4) / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hc : (3/4:ℝ) < 3/4 + d := by linarith
  have hOn : ContinuousOn LprimeOdd (Set.Ici (3/4 + d)) := by
    unfold LprimeOdd
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div
      · apply ContinuousOn.mul _ continuousOn_const
        apply Continuous.continuousOn
        exact (Real.continuous_const_rpow (by norm_num : (2:ℝ) ≠ 0)).comp continuous_neg
      · apply ContinuousOn.sub continuousOn_const
        apply Continuous.continuousOn
        exact (Real.continuous_const_rpow (by norm_num : (2:ℝ) ≠ 0)).comp continuous_neg
      · intro x hx
        have hxle : (3:ℝ)/4 + d ≤ x := hx
        have hx0 : (0:ℝ) < x := by linarith
        have hlt : (2:ℝ) ^ (-x) < 1 := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), inv_lt_one_iff₀]
          right
          exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
            (Or.inl ⟨by norm_num, hx0⟩)
        intro hcon
        rw [sub_eq_zero] at hcon
        linarith [hcon.symm ▸ hlt]
    · apply continuousOn_tsum
        (u := fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
          2 * Real.log ((q:ℕ):ℝ)
            / ((((q:ℕ):ℝ) ^ (3/4 + d) - 1) * ((((q:ℕ):ℝ) ^ (3/4 + d) - 2))))
        _ (logHodd2_deriv_summable (3/4 + d) hc)
      · intro q x hx
        have hxle : (3:ℝ)/4 + d ≤ x := hx
        have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
          have := q.2.2
          exact_mod_cast this
        have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
        have hPx := three_rpow_gt_two' _ hq3 x (by linarith)
        have hPc := three_rpow_gt_two' _ hq3 (3/4 + d) hc
        have hmono : ((q:ℕ):ℝ) ^ (3/4 + d) ≤ ((q:ℕ):ℝ) ^ x :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hxle
        have hlog : (0:ℝ) ≤ Real.log ((q:ℕ):ℝ) := by
          apply Real.log_nonneg; linarith
        rw [Real.norm_eq_abs, abs_div,
          abs_of_nonneg (by nlinarith [hPx] :
            (0:ℝ) ≤ (((q:ℕ):ℝ) ^ x - 1) * (((q:ℕ):ℝ) ^ x - 2))]
        have habs : |-2 * Real.log ((q:ℕ):ℝ)| = 2 * Real.log ((q:ℕ):ℝ) := by
          rw [abs_of_nonpos (by nlinarith [hlog])]
          ring
        rw [habs]
        apply div_le_div_of_nonneg_left (by linarith) (by nlinarith [hPc])
        nlinarith [hmono, hPc, hPx]
      · intro q
        have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
          have := q.2.2
          exact_mod_cast this
        have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
        apply ContinuousOn.div continuousOn_const
        · apply ContinuousOn.mul
          · apply ContinuousOn.sub _ continuousOn_const
            apply Continuous.continuousOn
            exact Real.continuous_const_rpow (ne_of_gt hq0)
          · apply ContinuousOn.sub _ continuousOn_const
            apply Continuous.continuousOn
            exact Real.continuous_const_rpow (ne_of_gt hq0)
        · intro x hx
          have hxle : (3:ℝ)/4 + d ≤ x := hx
          have hPx := three_rpow_gt_two' _ hq3 x (by linarith)
          intro hcon
          rcases mul_eq_zero.mp hcon with h | h
          · linarith [sub_eq_zero.mp h]
          · linarith [sub_eq_zero.mp h]
  apply (hOn.continuousAt _).continuousWithinAt
  apply Ici_mem_nhds
  rw [hd]; linarith

/-- Item 2: the prefactor's log-derivative at general s. -/
theorem prefactor_logderiv_gen (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => 2 * Real.log (1 - (2:ℝ) ^ (-t)))
      (2 * ((2:ℝ) ^ (-s) * Real.log 2 / (1 - (2:ℝ) ^ (-s)))) s := by
  have hb : (0:ℝ) < 2 := by norm_num
  have hlt : (2:ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (le_of_lt hb)]
    rw [inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow_iff_of_pos hb |>.mpr (Or.inl ⟨by norm_num, hs⟩)
  have hne : (1:ℝ) - (2:ℝ) ^ (-s) ≠ 0 := by
    intro hc
    rw [sub_eq_zero] at hc
    linarith [hc.symm ▸ hlt]
  have hpow : HasDerivAt (fun t : ℝ => (2:ℝ) ^ (-t))
      (-(Real.log 2 * (2:ℝ) ^ (-s))) s := by
    have h := HasDerivAt.const_rpow hb (hasDerivAt_neg s)
    simpa using h
  have hinner : HasDerivAt (fun t : ℝ => 1 - (2:ℝ) ^ (-t))
      (Real.log 2 * (2:ℝ) ^ (-s)) s := by
    simpa using hpow.const_sub 1
  have hlog := (hinner.log hne).const_mul 2
  have hval : 2 * (Real.log 2 * (2:ℝ) ^ (-s) / (1 - (2:ℝ) ^ (-s)))
      = 2 * ((2:ℝ) ^ (-s) * Real.log 2 / (1 - (2:ℝ) ^ (-s))) := by ring
  rw [← hval]
  exact hlog

/-- Item 3: the chain rule at general s in (3/4, 2). -/
theorem HoddR2_hasDerivAt_gen (s : ℝ) (hs : 3/4 < s) (hs2 : s < 2) :
    HasDerivAt HoddR2 (HoddR2 s * LprimeOdd s) s := by
  have h1 := prefactor_logderiv_gen s (by linarith)
  have h2 := logHodd2_hasDerivAt s hs hs2
  have hcongr : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-s) / (1 - 2 * ((q:ℕ):ℝ) ^ (-s))
        + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-s) / (1 - ((q:ℕ):ℝ) ^ (-s)))
      = -2 * Real.log ((q:ℕ):ℝ) / ((((q:ℕ):ℝ) ^ s - 1) * ((((q:ℕ):ℝ) ^ s - 2))) := by
    intro q
    exact prime_logderiv_forms_eq (q:ℕ) q.2.2 s hs
  rw [tsum_congr hcongr] at h2
  have hsum := h1.add h2
  have hexp := hsum.exp
  unfold HoddR2 LprimeOdd
  convert hexp using 1 <;> simp [Pi.add_apply]

/-- Item 4: deriv HoddR2 is continuous on (3/4, 2). -/
theorem HoddR2_deriv_continuousOn :
    ContinuousOn (fun s : ℝ => HoddR2 s * LprimeOdd s) (Set.Ioo (3/4 : ℝ) 2) := by
  apply ContinuousOn.mul _ LprimeOdd_continuousOn
  unfold HoddR2
  apply ContinuousOn.rexp
  apply ContinuousOn.add _ logHodd2_continuousOn
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log
  · apply ContinuousOn.sub continuousOn_const
    apply Continuous.continuousOn
    exact (Real.continuous_const_rpow (by norm_num : (2:ℝ) ≠ 0)).comp continuous_neg
  · intro x hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    have hlt : (2:ℝ) ^ (-x) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), inv_lt_one_iff₀]
      right
      exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hx0⟩)
    intro hc
    rw [sub_eq_zero] at hc
    linarith [hc.symm ▸ hlt]

/-! ### Step 4, items 6-8: the interchange and the limit -/

/-- Item 6: on (1,2), d_s Hodd(s,2) is the termwise sum.

hCoeff_hasSum gives the pointwise convergence at z = 2; the derivative series
is dominated by betaFam j * 2^j, summable by fam_summable. -/
theorem hCoeff_interchange (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hdiff : ∀ t : ℝ, 1 ≤ t →
      DifferentiableOn ℂ (fun w => Hodd t w) (Metric.ball 0 4))
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    HasDerivAt (fun t : ℝ => Hodd t 2)
      (∑' j : ℕ, deriv (fun x : ℝ => hCoeff x j) s * 2 ^ j) s := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn (s := Set.Ioo (1:ℝ) 2)
    (l := Filter.atTop) isOpen_Ioo
    (f := fun N : Finset ℕ => fun t : ℝ => ∑ j ∈ N, hCoeff t j * 2 ^ j)
    (f' := fun N : Finset ℕ => fun t : ℝ =>
      ∑ j ∈ N, deriv (fun x : ℝ => hCoeff x j) t * 2 ^ j)
    (g := fun t : ℝ => Hodd t 2)
    (g' := fun t : ℝ => ∑' j : ℕ, deriv (fun x : ℝ => hCoeff x j) t * 2 ^ j)
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo]
    intro K hKsub hKcomp
    apply tendstoUniformlyOn_tsum
      (u := fun j : ℕ => betaFam j * (2:ℝ) ^ j) hf.fam_summable
    intro j x hx
    have hxmem : x ∈ Set.Ioo (1:ℝ) 2 := hKsub hx
    rw [norm_mul]
    have hb := hf.deriv_bound j x hxmem
    have h2 : ‖((2:ℂ)) ^ j‖ = (2:ℝ) ^ j := by
      rw [norm_pow]
      norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  · filter_upwards with N t ht
    have hd : ∀ j ∈ N, HasDerivAt (fun x : ℝ => hCoeff x j * 2 ^ j)
        (deriv (fun x : ℝ => hCoeff x j) t * 2 ^ j) t := by
      intro j _
      exact (hf.deriv_exists j t ht).mul_const _
    have h := HasDerivAt.sum (u := N)
      (A := fun j : ℕ => fun x : ℝ => hCoeff x j * 2 ^ j)
      (A' := fun j : ℕ => deriv (fun x : ℝ => hCoeff x j) t * 2 ^ j) hd
    have hfn : (fun t : ℝ => ∑ j ∈ N, hCoeff t j * 2 ^ j)
        = ∑ j ∈ N, (fun x : ℝ => hCoeff x j * 2 ^ j) := by
      funext r
      rw [Finset.sum_apply]
    rw [hfn]
    exact h
  · intro t ht
    exact hCoeff_hasSum t (le_of_lt ht.1) 2 (by norm_num) (hdiff t (le_of_lt ht.1))
  · exact hs

/-- Item 7: the s -> 1+ limit of the coefficient-derivative sum.

Dominated convergence: termwise by tendsto_deriv, dominated by
betaFam j * 2^j. -/
theorem hCoeff_deriv_sum_limit (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd) :
    Filter.Tendsto
      (fun s : ℝ => ∑' j : ℕ, deriv (fun x : ℝ => hCoeff x j) s * 2 ^ j)
      (nhdsWithin 1 (Set.Ioo (1:ℝ) 2))
      (nhds (∑' j : ℕ, bHatOdd j * 2 ^ j)) := by
  apply tendsto_tsum_of_dominated_convergence hf.fam_summable
  · intro j
    apply ((hf.tendsto_deriv j).mul_const _).mono_left
    exact nhdsWithin_mono _ Set.Ioo_subset_Ioi_self
  · filter_upwards [self_mem_nhdsWithin] with t ht j
    rw [norm_mul]
    have hb := hf.deriv_bound j t ht
    have h2 : ‖((2:ℂ)) ^ j‖ = (2:ℝ) ^ j := by
      rw [norm_pow]
      norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_right hb (by positivity)

/-- The p-th Hodd factor at z = 2, general s: it is the cast of a real. -/
theorem Hodd_factor_at_two_gen (s : ℝ) (hs : 3/4 < s)
    (p : {p : ℕ // p.Prime ∧ 3 ≤ p}) :
    (1 - (2:ℂ) * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ)) : ℂ) ^ (2:ℂ)
      = ((((1 - 2 * ((p:ℕ):ℝ) ^ (-s))⁻¹ * (1 - ((p:ℕ):ℝ) ^ (-s)) ^ 2 : ℝ)) : ℂ) := by
  have hp3 : (3:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.property.2
  have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by linarith
  have hP := three_rpow_gt_two' _ hp3 s hs
  have hxv : ((p:ℕ):ℝ) ^ (-s) = 1 / ((p:ℕ):ℝ) ^ s := by
    rw [Real.rpow_neg (le_of_lt hp0), one_div]
  have hlt : ((p:ℕ):ℝ) ^ (-s) < 4/9 := by
    rw [hxv, div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hpos : (0:ℝ) < ((p:ℕ):ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have h1 : (0:ℝ) < 1 - ((p:ℕ):ℝ) ^ (-s) := by linarith
  have h2 : (0:ℝ) < 1 - 2 * ((p:ℕ):ℝ) ^ (-s) := by linarith
  have hsq : (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ)) : ℂ) ^ (2:ℂ)
      = (((1 - ((p:ℕ):ℝ) ^ (-s) : ℝ)) : ℂ) ^ (2:ℕ) := by
    rw [← Complex.cpow_natCast]
    norm_num
  rw [hsq]
  push_cast
  ring

/-- L'(1) = 2 log 2 - 2 S: the prefactor gives 2 log 2 and the prime sum
gives -2 S, by logHodd2_deriv_at_one. -/
theorem LprimeOdd_at_one : LprimeOdd 1 = 2 * Real.log 2 - 2 * Sodd := by
  unfold LprimeOdd
  have hpre : 2 * ((2:ℝ) ^ (-(1:ℝ)) * Real.log 2 / (1 - (2:ℝ) ^ (-(1:ℝ))))
      = 2 * Real.log 2 := by
    rw [Real.rpow_neg_one]
    norm_num
  have hcongr : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (-2 * Real.log ((q:ℕ):ℝ)
        / ((((q:ℕ):ℝ) ^ (1:ℝ) - 1) * ((((q:ℕ):ℝ) ^ (1:ℝ) - 2))))
      = -2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-(1:ℝ))
          / (1 - 2 * ((q:ℕ):ℝ) ^ (-(1:ℝ)))
        + 2 * Real.log ((q:ℕ):ℝ) * ((q:ℕ):ℝ) ^ (-(1:ℝ))
          / (1 - ((q:ℕ):ℝ) ^ (-(1:ℝ))) := by
    intro q
    exact (prime_logderiv_forms_eq (q:ℕ) q.2.2 1 (by norm_num)).symm
  rw [hpre, tsum_congr hcongr, logHodd2_deriv_at_one]
  ring

/-- Item 5': the C/R bridge.  Hodd s 2 is a product of positive reals, so it
is real and equals HoddR2 s.  Proved at s = 1 as HoddR2_at_one. -/
theorem HoddR2_eq_Hodd_two (s : ℝ) (hs : 3/4 < s) :
    ((HoddR2 s : ℝ) : ℂ) = Hodd s 2 := by
  have h2pos : (0:ℝ) < 1 - (2:ℝ) ^ (-s) := by
    have hs0 : (0:ℝ) < s := by linarith
    have hlt : (2:ℝ) ^ (-s) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), inv_lt_one_iff₀]
      right
      exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hs0⟩)
    linarith
  have hpos : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (0:ℝ) < (1 - 2 * ((q:ℕ):ℝ) ^ (-s))⁻¹ * (1 - ((q:ℕ):ℝ) ^ (-s)) ^ 2 := by
    intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
    have hP := three_rpow_gt_two' _ hq3 s hs
    have hxv : ((q:ℕ):ℝ) ^ (-s) = 1 / ((q:ℕ):ℝ) ^ s := by
      rw [Real.rpow_neg (le_of_lt hq0), one_div]
    have hlt : ((q:ℕ):ℝ) ^ (-s) < 4/9 := by
      rw [hxv, div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hp2 : (0:ℝ) < 1 - 2 * ((q:ℕ):ℝ) ^ (-s) := by linarith
    have hp1 : (0:ℝ) < 1 - ((q:ℕ):ℝ) ^ (-s) := by linarith
    positivity
  have hlogeq : ∀ q : {p : ℕ // p.Prime ∧ 3 ≤ p},
      Real.exp (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-s))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-s)))
      = (1 - 2 * ((q:ℕ):ℝ) ^ (-s))⁻¹ * (1 - ((q:ℕ):ℝ) ^ (-s)) ^ 2 := by
    intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by
      have := q.2.2
      exact_mod_cast this
    have hq0 : (0:ℝ) < ((q:ℕ):ℝ) := by linarith
    have hP := three_rpow_gt_two' _ hq3 s hs
    have hxv : ((q:ℕ):ℝ) ^ (-s) = 1 / ((q:ℕ):ℝ) ^ s := by
      rw [Real.rpow_neg (le_of_lt hq0), one_div]
    have hlt : ((q:ℕ):ℝ) ^ (-s) < 4/9 := by
      rw [hxv, div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hp2 : (0:ℝ) < 1 - 2 * ((q:ℕ):ℝ) ^ (-s) := by linarith
    have hp1 : (0:ℝ) < 1 - ((q:ℕ):ℝ) ^ (-s) := by linarith
    have hsq : Real.exp (2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-s)))
        = (1 - ((q:ℕ):ℝ) ^ (-s)) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hp1]
      ring
    rw [Real.exp_add, Real.exp_neg, Real.exp_log hp2, hsq]
  have hsum : HasSum (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      -Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-s))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-s))) (logHodd2 s) :=
    (logHodd2_summable s hs).hasSum
  have hprod := hasProd_rexp_of_hasSum hsum
  have hfe : (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} => Real.exp
      (-Real.log (1 - 2 * ((q:ℕ):ℝ) ^ (-s))
        + 2 * Real.log (1 - ((q:ℕ):ℝ) ^ (-s))))
      = fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        (1 - 2 * ((q:ℕ):ℝ) ^ (-s))⁻¹ * (1 - ((q:ℕ):ℝ) ^ (-s)) ^ 2 := by
    funext q
    exact hlogeq q
  rw [hfe] at hprod
  unfold HoddR2 Hodd
  rw [Real.exp_add]
  have hpre : Real.exp (2 * Real.log (1 - (2:ℝ) ^ (-s)))
      = (1 - (2:ℝ) ^ (-s)) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log h2pos]
    ring
  rw [hpre, ← hprod.tprod_eq]
  have hmul : Multipliable (fun q : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 * ((q:ℕ):ℝ) ^ (-s))⁻¹ * (1 - ((q:ℕ):ℝ) ^ (-s)) ^ 2) :=
    hprod.multipliable
  have hmt := hmul.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  simp only [Complex.ofRealHom_eq_coe] at hmt
  rw [Complex.ofReal_mul, hmt]
  congr 1
  · have hsq : (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) ^ (2:ℂ)
        = (((1 - (2:ℝ) ^ (-s) : ℝ)) : ℂ) ^ (2:ℕ) := by
      rw [← Complex.cpow_natCast]
      norm_num
    rw [hsq]
    push_cast
    ring
  · apply tprod_congr
    intro q
    exact (Hodd_factor_at_two_gen s hs q).symm

/-- The bridge on derivatives. -/
theorem HoddR2_deriv_bridge (s : ℝ) (hs : 3/4 < s) (L : ℝ)
    (h : HasDerivAt HoddR2 L s) :
    HasDerivAt (fun t : ℝ => Hodd t 2) ((L : ℂ)) s := by
  have hcast : HasDerivAt (fun t : ℝ => ((HoddR2 t : ℝ) : ℂ)) ((L : ℂ)) s :=
    h.ofReal_comp
  apply hcast.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi (a := (3/4 : ℝ))).mem_nhds hs] with t ht
  exact (HoddR2_eq_Hodd_two t ht).symm


/-- STEP 4: sum_j b_j 2^j = 2 d (log 2 - S). -/
theorem bHatOdd_sum_two (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hdiff : ∀ t : ℝ, 1 ≤ t →
      DifferentiableOn ℂ (fun w => Hodd t w) (Metric.ball 0 4)) :
    (∑' j : ℕ, bHatOdd j * 2 ^ j)
      = ((2 * dConst * (Real.log 2 - Sodd) : ℝ) : ℂ) := by
  have hlim := hCoeff_deriv_sum_limit betaFam bHatOdd hf
  have heq : ∀ t ∈ Set.Ioo (1:ℝ) 2,
      (∑' j : ℕ, deriv (fun x : ℝ => hCoeff x j) t * 2 ^ j)
        = deriv (fun r : ℝ => Hodd r 2) t := by
    intro t ht
    exact ((hCoeff_interchange betaFam bHatOdd hf hdiff t ht).deriv).symm
  have hlim' : Filter.Tendsto (fun t : ℝ => deriv (fun r : ℝ => Hodd r 2) t)
      (nhdsWithin 1 (Set.Ioo (1:ℝ) 2))
      (nhds (∑' j : ℕ, bHatOdd j * 2 ^ j)) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact heq t ht
  have hcont : Filter.Tendsto (fun t : ℝ => deriv (fun r : ℝ => Hodd r 2) t)
      (nhdsWithin 1 (Set.Ioo (1:ℝ) 2))
      (nhds (((2 * dConst * (Real.log 2 - Sodd) : ℝ) : ℂ))) := by
    -- on (1,2) the derivative is the real quantity HoddR2 * LprimeOdd, cast
    have hval : ∀ t ∈ Set.Ioo (1:ℝ) 2,
        deriv (fun r : ℝ => Hodd r 2) t = (((HoddR2 t * LprimeOdd t : ℝ)) : ℂ) := by
      intro t ht
      have hgen := HoddR2_hasDerivAt_gen t (by linarith [ht.1]) ht.2
      exact (HoddR2_deriv_bridge t (by linarith [ht.1]) _ hgen).deriv
    -- the real function is continuous at 1, with value dConst * (2 log2 - 2 S)
    have hR : Filter.Tendsto (fun t : ℝ => HoddR2 t * LprimeOdd t)
        (nhdsWithin 1 (Set.Ioo (1:ℝ) 2))
        (nhds (HoddR2 1 * LprimeOdd 1)) := by
      have hc := HoddR2_deriv_continuousOn 1 (by norm_num)
      apply hc.mono_left
      apply nhdsWithin_mono
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    have hvalue : HoddR2 1 * LprimeOdd 1 = 2 * dConst * (Real.log 2 - Sodd) := by
      rw [HoddR2_at_one, LprimeOdd_at_one]
      ring
    rw [hvalue] at hR
    have hcast := (Complex.continuous_ofReal.tendsto _).comp hR
    apply hcast.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply]
    exact (hval t ht).symm
  have hnb : (nhdsWithin (1:ℝ) (Set.Ioo 1 2)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (by norm_num : (1:ℝ) ≠ 2)]
    exact ⟨le_refl 1, by norm_num⟩
  exact tendsto_nhds_unique hlim' hcont

/-! ### Step 5: the coefficient of 2^-k

Substituting the two expansions into fOdd_u_form and integrating termwise:

  order e^-u : sum_j h_j(1) = H(1,1) = 1/2                [hCoeff_sum_one]

  order e^-2u: 2^-(k+1) * sum_j (b_j + 2 gamma h_j(1)) 2^j
             = 2^-(k+1) * [2d(log2 - S) + 2 gamma d]      [bHatOdd_sum_two,
                                                           hCoeff_sum_two]
             = 2^-k * d(log2 - S + gamma) = beta 2^-k

  order e^-ju, j >= 3: O(3^-(k+1)) each                   [gamma_normalised_three]

The 2 gamma comes from the Jacobian (jacobian_u_signed) and the b_j from the
coefficient expansion (hCoeff_taylor); each is halved by the 2^-(m+1) of the
second Gamma integral, which is why beta carries d(log2 - S + gamma) rather
than twice it. -/

/-- The order-2 coefficient, assembled from step 4 and hCoeff_sum_two. -/
theorem order_two_coefficient (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hdiff : ∀ t : ℝ, 1 ≤ t →
      DifferentiableOn ℂ (fun w => Hodd t w) (Metric.ball 0 4))
    (hd1 : DifferentiableOn ℂ (fun w => Hodd 1 w) (Metric.ball 0 4)) :
    (∑' j : ℕ, bHatOdd j * 2 ^ j)
      + 2 * ((Real.eulerMascheroniConstant : ℝ) : ℂ)
          * (∑' j : ℕ, hCoeff 1 j * 2 ^ j)
      = ((2 * betaOdd : ℝ) : ℂ) := by
  rw [bHatOdd_sum_two betaFam bHatOdd hf hdiff]
  rw [(hCoeff_sum_two hd1).tsum_eq]
  unfold betaOdd
  push_cast
  ring

/-! ### Step 5: the integration

From fOdd_u_form,

  fOdd k = ∫_{Ioi 0} [Σ_j (h_j(s(u))).re u^{k-j}/(k-j)!] J(u) du

Substituting h_j(s(u)) = h_j(1) + ε(u) b_j + O(ε²) [hCoeff_taylor] and
J(u) = e^-u + 2γ e^-2u + O(e^-3u) [jacobian_u_signed], the product expands as

  MAIN1 : [Σ_j h_j(1) u^{k-j}/(k-j)!] e^-u
  MAIN2 : [Σ_j (b_j + 2γ h_j(1)) u^{k-j}/(k-j)!] e^-2u
  ERR   : everything else, each factor O(e^-3u) times a polynomial in u.

MAIN1 integrates to Σ_j h_j(1) = 1/2 by gamma_normalised and hCoeff_sum_one.
MAIN2 integrates to 2^{-(k+1)} Σ_j (b_j + 2γ h_j(1)) 2^j = β 2^-k by
gamma_normalised_two and order_two_coefficient.
ERR is bounded by gamma_normalised_three. -/

/-- The main term at order e^-u integrates to 1/2. -/
theorem main_term_one (k : ℕ) (hk : 1 ≤ k)
    (hd1 : DifferentiableOn ℂ (fun w => Hodd 1 w) (Metric.ball 0 4)) :
    ∑ j ∈ Finset.range (k + 1),
        (hCoeff 1 j).re * (∫ u in Set.Ioi (0:ℝ), u ^ (k - j) * Real.exp (-u))
          / (Nat.factorial (k - j))
      = ∑ j ∈ Finset.range (k + 1), (hCoeff 1 j).re :=
  fOdd_leading_order k hk

/-- The main term at order e^-2u carries the factor 2^-(k+1). -/
theorem main_term_two (k : ℕ) (c : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k + 1),
        c j * (∫ u in Set.Ioi (0:ℝ), u ^ (k - j) * Real.exp (-(2 * u)))
          / (Nat.factorial (k - j))
      = ∑ j ∈ Finset.range (k + 1), c j * (1 / 2 ^ (k - j + 1)) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero (k - j))]
  have hg := gamma_normalised_two (k - j)
  rw [div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero (k - j))] at hg
  rw [mul_assoc, hg]

/-- The integrand of fOdd_u_form, split into its two main terms and the
remainder.  Every piece of the split is an identity; the content is in
bounding `rest`. -/
noncomputable def oddSplitMain1 (k : ℕ) (u : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1),
    (hCoeff 1 j).re * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-u)

noncomputable def oddSplitMain2 (bHatOdd : ℕ → ℂ) (k : ℕ) (u : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1),
    ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
      * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-2 * u)

/-- MAIN1 and MAIN2 are integrable on Ioi 0: finite sums of u^m e^(-cu),
each a Gamma integral. -/
theorem oddSplitMain_integrable (bHatOdd : ℕ → ℂ) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => oddSplitMain1 k u) (Set.Ioi (0:ℝ)) ∧
    MeasureTheory.IntegrableOn (fun u : ℝ => oddSplitMain2 bHatOdd k u) (Set.Ioi (0:ℝ)) := by
  have hterm : ∀ (c : ℝ), 1 ≤ c → ∀ (C : ℕ → ℝ),
      MeasureTheory.IntegrableOn
        (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          C j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-c * u))
        (Set.Ioi (0:ℝ)) := by
    intro c hc C
    have hrw : ∀ u : ℝ,
        (∑ j ∈ Finset.range (k + 1),
          C j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-c * u)
        = ∑ j ∈ Finset.range (k + 1),
          (C j / (Nat.factorial (k - j)) * (u ^ (k - j) * Real.exp (-(c * u)))) := by
      intro u
      have hcu : (-c : ℝ) * u = -(c * u) := by ring
      rw [hcu, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    apply MeasureTheory.IntegrableOn.congr_fun _ (fun u _ => (hrw u).symm)
      measurableSet_Ioi
    apply MeasureTheory.integrable_finset_sum
    intro j _
    apply MeasureTheory.Integrable.const_mul
    have hgam : MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-x) * x ^ (((k - j : ℕ) : ℝ) + 1 - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (by positivity)
    simp only [add_sub_cancel_right] at hgam
    have hgam' : MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ ((k - j : ℕ)) * Real.exp (-x)) (Set.Ioi 0) := by
      apply hgam.congr_fun _ measurableSet_Ioi
      intro x _
      simp only
      rw [← Real.rpow_natCast x (k - j)]
      ring
    apply MeasureTheory.Integrable.mono hgam'
    · apply MeasureTheory.AEStronglyMeasurable.mul <;>
        (apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0:ℝ) < x := hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos (-(c*x))), abs_of_pos (Real.exp_pos (-x))]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [hc, hx0]
  constructor
  · unfold oddSplitMain1
    have := hterm 1 (by norm_num) (fun j => (hCoeff 1 j).re)
    simpa using this
  · unfold oddSplitMain2
    exact hterm 2 (by norm_num)
      (fun j => (bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)

/-- MAIN1 integrates to the PARTIAL sum of the h_j(1).

Note this is the partial sum over j <= k, not the full series: the difference
Sum_{j>k} h_j(1) is exponentially small (Cauchy, |h_j| <= M/3^j) and joins the
remainder rather than vanishing. -/
theorem oddSplitMain1_integral (k : ℕ) (hk : 1 ≤ k) :
    (∫ u in Set.Ioi (0:ℝ), oddSplitMain1 k u)
      = ∑ j ∈ Finset.range (k + 1), (hCoeff 1 j).re := by
  unfold oddSplitMain1
  have hrw : ∀ u : ℝ,
      (∑ j ∈ Finset.range (k + 1),
        (hCoeff 1 j).re * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-u)
      = ∑ j ∈ Finset.range (k + 1),
        ((hCoeff 1 j).re / (Nat.factorial (k - j)) * (u ^ (k - j) * Real.exp (-u))) := by
    intro u
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => hrw u)]
  rw [MeasureTheory.integral_finsetSum]
  · rw [← fOdd_leading_order k hk]
    apply Finset.sum_congr rfl
    intro j _
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro j _
    have hgam : MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-x) * x ^ (((k - j : ℕ) : ℝ) + 1 - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (by positivity)
    simp only [add_sub_cancel_right] at hgam
    have hgam' : MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ ((k - j : ℕ)) * Real.exp (-x)) (Set.Ioi 0) := by
      apply hgam.congr_fun _ measurableSet_Ioi
      intro x _
      simp only
      rw [← Real.rpow_natCast x (k - j)]
      ring
    exact hgam'.const_mul _

/-- MAIN2 integrates to 2^-(k+1) times the PARTIAL sum, again not the full
series; the tail joins the remainder. -/
theorem oddSplitMain2_integral (bHatOdd : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (∫ u in Set.Ioi (0:ℝ), oddSplitMain2 bHatOdd k u)
      = (1 / 2 ^ (k + 1)) * ∑ j ∈ Finset.range (k + 1),
          (((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
            * 2 ^ j) := by
  unfold oddSplitMain2
  set c : ℕ → ℝ := fun j =>
    (bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re with hc
  have hrw : ∀ u : ℝ,
      (∑ j ∈ Finset.range (k + 1),
        c j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-2 * u)
      = ∑ j ∈ Finset.range (k + 1),
        (c j / (Nat.factorial (k - j)) * (u ^ (k - j) * Real.exp (-(2 * u)))) := by
    intro u
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have : (-2 : ℝ) * u = -(2 * u) := by ring
    rw [this]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => hrw u)]
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : (2:ℝ) ^ (k - j) * 2 ^ j = 2 ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [MeasureTheory.integral_const_mul]
    have hg := gamma_normalised_two (k - j)
    rw [div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero (k - j))] at hg
    rw [hg]
    have hfne : ((Nat.factorial (k - j) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (k - j)
    field_simp
    simp only [hc]
    linear_combination (-(2 * (bHatOdd j).re
      + 4 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)) * hpow
  · intro j _
    have hgam : MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-x) * x ^ (((k - j : ℕ) : ℝ) + 1 - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (by positivity)
    simp only [add_sub_cancel_right] at hgam
    have hgam' : MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ ((k - j : ℕ)) * Real.exp (-x)) (Set.Ioi 0) := by
      apply hgam.congr_fun _ measurableSet_Ioi
      intro x _
      simp only
      rw [← Real.rpow_natCast x (k - j)]
      ring
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.mono hgam'
    · apply MeasureTheory.AEStronglyMeasurable.mul <;>
        (apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0:ℝ) < x := hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos (-(2*x))), abs_of_pos (Real.exp_pos (-x))]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      linarith

/-! The two main integrals give PARTIAL sums.  Passing to the full series --
where hCoeff_sum_one gives 1/2 and order_two_coefficient gives 2 beta -- costs
two tail terms,

    Sum_{j>k} h_j(1)      and    Sum_{j>k} (b_j + 2 gamma h_j(1)) 2^j,

both exponentially small by the Cauchy bound |h_j| <= M/3^j (and its
derivative analogue).  These join the remainder in fOdd_expansion_final.

A second point the split must handle: jacobian_u_signed and eps_of_u_signed
hold only for u >= U.  The integral over Ioi 0 therefore splits at U, and the
piece on Ioc 0 U -- which is where s is large, not where the expansion lives --
needs its own bound. -/

/-! ### Step 5: the tail bounds

MAIN1 and MAIN2 give partial sums over j <= k.  Passing to the full series
costs two tails, and fam_decay supplies their rate. -/

/-- The coefficient tail beyond k, from the Cauchy bound at radius 3. -/
theorem geom_tail_bound_cx (f : ℕ → ℂ) (D r : ℝ) (hD : 0 ≤ D)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ j : ℕ, ‖f j‖ ≤ D * r ^ j) (k : ℕ) :
    ‖∑' j : ℕ, (if k < j then f j else 0)‖ ≤ D * r ^ (k+1) / (1 - r) := by
  have hsum : Summable (fun j : ℕ => D * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left D
  have hfs : Summable (fun j : ℕ => ‖(if k < j then f j else 0)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
    intro j
    by_cases hj : k < j
    · simp only [hj, if_true]; exact hb j
    · simp only [hj, if_false, norm_zero]
      positivity
  have hmaj : Summable (fun j : ℕ => (if k < j then D * r ^ j else 0)) := by
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro j
      by_cases hj : k < j
      · simp only [hj, if_true]; positivity
      · simp only [hj, if_false]; exact le_refl _
    · intro j
      by_cases hj : k < j
      · simp only [hj, if_true]; exact le_refl _
      · simp only [hj, if_false]; positivity
  have hle : ∀ j : ℕ, ‖(if k < j then f j else 0)‖
      ≤ (if k < j then D * r ^ j else 0) := by
    intro j
    by_cases hj : k < j
    · simp only [hj, if_true]; exact hb j
    · simp only [hj, if_false, norm_zero]; exact le_refl 0
  calc ‖∑' j : ℕ, (if k < j then f j else 0)‖
      ≤ ∑' j : ℕ, ‖(if k < j then f j else 0)‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' j : ℕ, (if k < j then D * r ^ j else 0) := by
        exact Summable.tsum_le_tsum hle hfs hmaj
    _ = D * r ^ (k+1) / (1 - r) := by
        have hsplit := hmaj.sum_add_tsum_nat_add (k+1)
        have hzero : ∑ j ∈ Finset.range (k+1),
            (if k < j then D * r ^ j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have : j < k + 1 := Finset.mem_range.mp hj
          have hnk : ¬ (k < j) := by omega
          simp only [hnk, if_false]
        rw [hzero, zero_add] at hsplit
        have hshift : ∀ i : ℕ,
            (if k < i + (k + 1) then D * r ^ (i + (k + 1)) else 0)
              = D * r ^ (k+1) * r ^ i := by
          intro i
          have hlt : k < i + (k + 1) := by omega
          simp only [hlt, if_true]
          rw [pow_add]
          ring
        rw [← hsplit, tsum_congr hshift, tsum_mul_left,
          tsum_geometric_of_lt_one hr0 hr1]
        rw [div_eq_mul_inv]

/-- The coefficient tail beyond k, from the Cauchy bound at radius 3. -/
theorem hCoeff_tail_bound (C : ℝ) (hC : 0 ≤ C)
    (hcb : ∀ j : ℕ, ‖hCoeff 1 j‖ ≤ C * ((1:ℝ)/3) ^ j) (k : ℕ) :
    ‖∑' j : ℕ, (if k < j then hCoeff 1 j else 0)‖
      ≤ C * ((1:ℝ)/3) ^ (k+1) / (1 - 1/3) :=
  geom_tail_bound_cx (fun j => hCoeff 1 j) C (1/3) hC (by norm_num) (by norm_num) hcb k

/-- The derivative tail beyond k, from fam_decay. -/
theorem bHatOdd_tail_bound (bHatOdd : ℕ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hdec : ∀ j : ℕ, ‖bHatOdd j * 2 ^ j‖ ≤ D * ((2:ℝ)/3) ^ j) (k : ℕ) :
    ‖∑' j : ℕ, (if k < j then bHatOdd j * 2 ^ j else 0)‖
      ≤ D * ((2:ℝ)/3) ^ (k+1) / (1 - 2/3) :=
  geom_tail_bound_cx (fun j => bHatOdd j * 2 ^ j) D (2/3) hD (by norm_num)
    (by norm_num) hdec k

/-! ### Step 3: the coefficient sum, by finite algebra

PROOF.md (5.5).  With g the convolution of h'' against the coefficients of
(1 - z/3)^3 = 1 - z + z^2/3 - z^3/27, the inverse convolution recovers h'':

    h_j'' = sum_{i<=j} g_i C(j-i+2,2) 3^-(j-i)

because (1,-1,1/3,-1/27) and (C(m+2,2) 3^-m) are convolution inverses.  This
is finite algebra: no analyticity of G_2 enters. -/

/-- The coefficients of (1 - z/3)^3. -/
noncomputable def poleCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 1/3
  | 3 => -1/27
  | _ => 0

/-- The coefficients of (1 - z/3)^(-3). -/
noncomputable def invPoleCoeff (m : ℕ) : ℝ :=
  (Nat.choose (m + 2) 2 : ℝ) * ((1:ℝ)/3) ^ m

/-- C(m+2,2) as a quadratic over the reals. -/
theorem choose_two_real (m : ℕ) :
    (Nat.choose (m + 2) 2 : ℝ) = ((m:ℝ) + 2) * ((m:ℝ) + 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.choose_succ_succ' (n + 2) 1,
        Nat.choose_one_right]
      push_cast at ih ⊢
      linarith [ih]

/-- C(m+3,3) as a cubic over the reals, by Pascal and choose_two_real. -/
theorem choose_three_real (m : ℕ) :
    (Nat.choose (m + 3) 3 : ℝ) = ((m:ℝ) + 3) * ((m:ℝ) + 2) * ((m:ℝ) + 1) / 6 := by
  induction m with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 by ring, Nat.choose_succ_succ' (n + 3) 2]
      have h2 := choose_two_real (n + 1)
      push_cast at ih h2 ⊢
      linarith [ih, h2]

/-- Hockey stick: sum_{m<=n} C(m+2,2) = C(n+3,3). -/
theorem hockey_stick (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (Nat.choose (m + 2) 2 : ℝ)
      = (Nat.choose (n + 3) 3 : ℝ) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : Nat.choose (m + 1 + 3) 3
          = Nat.choose (m + 3) 3 + Nat.choose (m + 3) 2 := by
        rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.choose_succ_succ' (m + 3) 2]
        ring
      rw [hp]
      push_cast
      have : (Nat.choose (m + 3) 2 : ℝ) = (Nat.choose (m + 1 + 2) 2 : ℝ) := by
        norm_num
      linarith [this]

/-- poleCoeff vanishes from index 4 on. -/
theorem poleCoeff_zero (t : ℕ) (ht : 4 ≤ t) : poleCoeff t = 0 := by
  match t, ht with
  | (m+4), _ => rfl

/-- (a) The two coefficient sequences are convolution inverses.

For n >= 4 only t = 0,1,2,3 contribute, and the bracket

    (n+2)(n+1) - 3n(n+1) + 3n(n-1) - (n-1)(n-2)

is the third finite difference of a quadratic, hence identically zero. -/
theorem poleCoeff_conv (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), poleCoeff t * invPoleCoeff (n - t)
      = if n = 0 then 1 else 0 := by
  have hc : ∀ m : ℕ, invPoleCoeff m
      = (((m:ℝ) + 2) * ((m:ℝ) + 1) / 2) * ((1:ℝ)/3) ^ m := by
    intro m; rw [invPoleCoeff, choose_two_real]
  match n with
  | 0 => norm_num [poleCoeff, hc]
  | 1 =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num [poleCoeff, hc]
  | 2 =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num [poleCoeff, hc]
  | 3 =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      norm_num [poleCoeff, hc]
  | (m+4) =>
      have hsub : Finset.range 4 ⊆ Finset.range (m + 4 + 1) := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      have hvanish : ∀ x ∈ Finset.range (m + 4 + 1), x ∉ Finset.range 4 →
          poleCoeff x * invPoleCoeff (m + 4 - x) = 0 := by
        intro x _ hx
        rcases Nat.lt_or_ge x 4 with h | h
        · exact absurd (Finset.mem_range.mpr h) hx
        · rw [poleCoeff_zero x h, zero_mul]
      rw [← Finset.sum_subset hsub hvanish]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      have e0 : m + 4 - 0 = m + 4 := by omega
      have e1 : m + 4 - 1 = m + 3 := by omega
      have e2 : m + 4 - 2 = m + 2 := by omega
      have e3 : m + 4 - 3 = m + 1 := by omega
      rw [e0, e1, e2, e3]
      simp only [poleCoeff, hc]
      have p4 : ((1:ℝ)/3) ^ (m+4) = ((1:ℝ)/3) ^ m * (1/81) := by
        rw [pow_add]; norm_num
      have p3 : ((1:ℝ)/3) ^ (m+3) = ((1:ℝ)/3) ^ m * (1/27) := by
        rw [pow_add]; norm_num
      have p2 : ((1:ℝ)/3) ^ (m+2) = ((1:ℝ)/3) ^ m * (1/9) := by
        rw [pow_add]; norm_num
      have p1 : ((1:ℝ)/3) ^ (m+1) = ((1:ℝ)/3) ^ m * (1/3) := by
        rw [pow_add]; norm_num
      rw [p4, p3, p2, p1]
      push_cast
      ring

/-- The convolution of a sequence against poleCoeff. -/
noncomputable def poleConv (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (i + 1), poleCoeff t * a (i - t)

/-- (b) The inverse convolution recovers a.

Since poleCoeff and invPoleCoeff are convolution inverses (poleCoeff_conv),
convolving g = poleConv a against invPoleCoeff returns a. -/
theorem convInverse (a : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), poleConv a i * invPoleCoeff (j - i) = a j := by
  -- extend each inner sum to the full range so Finset.sum_comm applies
  have hext : ∀ i ∈ Finset.range (j + 1),
      poleConv a i * invPoleCoeff (j - i)
        = ∑ t ∈ Finset.range (j + 1),
            (if t ≤ i then poleCoeff t * a (i - t) * invPoleCoeff (j - i) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [poleConv, Finset.sum_mul]
    have hsub : Finset.range (i + 1) ⊆ Finset.range (j + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      rw [if_pos (by omega)]
    · intro x _ hx
      rw [Finset.mem_range] at hx
      rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  -- for fixed t, drop the indicator (range -> Ico) and shift i = t + u
  have hinner : ∀ t ∈ Finset.range (j + 1),
      (∑ i ∈ Finset.range (j + 1),
        (if t ≤ i then poleCoeff t * a (i - t) * invPoleCoeff (j - i) else 0))
      = ∑ u ∈ Finset.range (j + 1 - t),
          poleCoeff t * a u * invPoleCoeff (j - t - u) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hIco : Finset.Ico t (j + 1) ⊆ Finset.range (j + 1) := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range]
      omega
    have hfil : ∑ i ∈ Finset.range (j + 1),
        (if t ≤ i then poleCoeff t * a (i - t) * invPoleCoeff (j - i) else 0)
        = ∑ i ∈ Finset.Ico t (j + 1),
            poleCoeff t * a (i - t) * invPoleCoeff (j - i) := by
      rw [← Finset.sum_subset hIco]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Ico] at hi
        rw [if_pos hi.1]
      · intro x hx hnx
        rw [Finset.mem_range] at hx
        rw [Finset.mem_Ico] at hnx
        rw [if_neg (by omega)]
    rw [hfil, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Nat.add_sub_cancel_left, ← Nat.sub_sub]
  rw [Finset.sum_congr rfl hinner]
  -- extend the inner range to the full square, swap, then collapse by
  -- poleCoeff_conv: for fixed u the t-sum is 1 if u = j and 0 otherwise.
  have hext2 : ∀ t ∈ Finset.range (j + 1),
      (∑ u ∈ Finset.range (j + 1 - t),
        poleCoeff t * a u * invPoleCoeff (j - t - u))
      = ∑ u ∈ Finset.range (j + 1),
          (if t + u ≤ j then poleCoeff t * a u * invPoleCoeff (j - t - u) else 0) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hsub : Finset.range (j + 1 - t) ⊆ Finset.range (j + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_range] at hu
      rw [if_pos (by omega)]
    · intro x _ hx
      rw [Finset.mem_range] at hx
      rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hext2, Finset.sum_comm]
  have hcollapse : ∀ u ∈ Finset.range (j + 1),
      (∑ t ∈ Finset.range (j + 1),
        (if t + u ≤ j then poleCoeff t * a u * invPoleCoeff (j - t - u) else 0))
      = a u * (if j - u = 0 then 1 else 0) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hsub : Finset.range (j - u + 1) ⊆ Finset.range (j + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · rw [← poleCoeff_conv (j - u), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      rw [if_pos (by omega)]
      have : j - t - u = j - u - t := by omega
      rw [this]
      ring
    · intro x _ hx
      rw [Finset.mem_range] at hx
      rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hcollapse]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    rw [Finset.mem_range] at hb
    rw [if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ j) h

/-- invPoleCoeff (j-i) * 3^j = C(j-i+2,2) * 3^i for i <= j. -/
theorem invPoleCoeff_scale (i j : ℕ) (hij : i ≤ j) :
    invPoleCoeff (j - i) * (3:ℝ) ^ j
      = (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i := by
  rw [invPoleCoeff]
  have hp : ((1:ℝ)/3) ^ (j - i) * (3:ℝ) ^ j = (3:ℝ) ^ i := by
    have hji : i + (j - i) = j := by omega
    have h3 : ((3:ℝ) ^ (j - i)) ≠ 0 := by positivity
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_eq_iff h3, ← pow_add, hji]
  calc (Nat.choose (j - i + 2) 2 : ℝ) * ((1:ℝ)/3) ^ (j - i) * (3:ℝ) ^ j
      = (Nat.choose (j - i + 2) 2 : ℝ) * (((1:ℝ)/3) ^ (j - i) * (3:ℝ) ^ j) := by ring
    _ = (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i := by rw [hp]

/-- (d) The coefficient sum bound, PROOF.md (5.5). -/
theorem coeffSum_bound (a : ℕ → ℝ) (k : ℕ) (S : ℝ)
    (hS : ∑ i ∈ Finset.range (k + 1), |poleConv a i| * (3:ℝ) ^ i ≤ S) :
    ∑ j ∈ Finset.range (k + 1), |a j| * (3:ℝ) ^ j
      ≤ (Nat.choose (k + 3) 3 : ℝ) * S := by
  -- |a j| 3^j <= sum_{i<=j} |g i| C(j-i+2,2) 3^i, then swap and hockey_stick
  have hstep : ∀ j ∈ Finset.range (k + 1), |a j| * (3:ℝ) ^ j
      ≤ ∑ i ∈ Finset.range (k + 1),
          (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
           else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hsub : Finset.range (j + 1) ⊆ Finset.range (k + 1) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub (by
      intro x _ hx
      rw [Finset.mem_range] at hx
      rw [if_neg (by omega)])]
    have hexp : ∀ i ∈ Finset.range (j + 1),
        (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
         else 0)
        = |poleConv a i * invPoleCoeff (j - i)| * (3:ℝ) ^ j := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega), abs_mul]
      have hnn : |invPoleCoeff (j - i)| = invPoleCoeff (j - i) := by
        rw [abs_of_nonneg]
        rw [invPoleCoeff]; positivity
      rw [hnn]
      have := invPoleCoeff_scale i j (by omega)
      calc |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
          = |poleConv a i| * ((Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i) := by ring
        _ = |poleConv a i| * (invPoleCoeff (j - i) * (3:ℝ) ^ j) := by rw [this]
        _ = |poleConv a i| * invPoleCoeff (j - i) * (3:ℝ) ^ j := by ring
    rw [Finset.sum_congr rfl hexp, ← Finset.sum_mul, ← convInverse a j]
    exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  calc ∑ j ∈ Finset.range (k + 1), |a j| * (3:ℝ) ^ j
      ≤ ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
          (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
           else 0) := Finset.sum_le_sum hstep
    _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
           else 0) := Finset.sum_comm
    _ ≤ (Nat.choose (k + 3) 3 : ℝ) * S := by
        have hrow : ∀ i ∈ Finset.range (k + 1),
            (∑ j ∈ Finset.range (k + 1),
              (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
               else 0))
            ≤ (Nat.choose (k + 3) 3 : ℝ) * (|poleConv a i| * (3:ℝ) ^ i) := by
          intro i hi
          rw [Finset.mem_range] at hi
          -- restrict to Ico i (k+1), shift, then hockey_stick
          have hIco : Finset.Ico i (k + 1) ⊆ Finset.range (k + 1) := by
            intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_range]; omega
          rw [← Finset.sum_subset hIco (by
            intro x hx hnx
            rw [Finset.mem_range] at hx
            rw [Finset.mem_Ico] at hnx
            rw [if_neg (by omega)])]
          have hin : ∀ j ∈ Finset.Ico i (k + 1),
              (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
               else 0)
              = (Nat.choose (j - i + 2) 2 : ℝ) * (|poleConv a i| * (3:ℝ) ^ i) := by
            intro j hj
            rw [Finset.mem_Ico] at hj
            rw [if_pos hj.1]
            ring
          rw [Finset.sum_congr rfl hin, ← Finset.sum_mul,
            Finset.sum_Ico_eq_sum_range]
          have hshift : ∀ m ∈ Finset.range (k + 1 - i),
              (Nat.choose (i + m - i + 2) 2 : ℝ) = (Nat.choose (m + 2) 2 : ℝ) := by
            intro m _
            congr 2
            omega
          rw [Finset.sum_congr rfl hshift]
          have hk1 : k + 1 - i = (k - i) + 1 := by omega
          rw [hk1, hockey_stick]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : Nat.choose (k - i + 3) 3 ≤ Nat.choose (k + 3) 3 :=
            Nat.choose_le_choose 3 (by omega)
          exact_mod_cast this
        calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if i ≤ j then |poleConv a i| * (Nat.choose (j - i + 2) 2 : ℝ) * (3:ℝ) ^ i
               else 0)
            ≤ ∑ i ∈ Finset.range (k + 1),
                (Nat.choose (k + 3) 3 : ℝ) * (|poleConv a i| * (3:ℝ) ^ i) :=
              Finset.sum_le_sum hrow
          _ = (Nat.choose (k + 3) 3 : ℝ)
                * ∑ i ∈ Finset.range (k + 1), |poleConv a i| * (3:ℝ) ^ i := by
              rw [← Finset.mul_sum]
          _ ≤ (Nat.choose (k + 3) 3 : ℝ) * S :=
              mul_le_mul_of_nonneg_left hS (by positivity)

/-! ### The remaining leaves of fOdd_expansion_final

Each is stated so the interface is fixed; the proofs are the work that
remains.  The certified input is stated about betaFam, which is what
odd-proof/numerics/hcoeff_recursion.py computes (sup over s-boxes of the
convolution, then summed against 3^i). -/

/-- The certified coefficient sum, PROOF.md (5.5) with a = betaFam. -/
def CoeffSumCertified (betaFam : ℕ → ℝ) (S : ℝ) : Prop :=
  ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), |poleConv betaFam i| * (3:ℝ) ^ i ≤ S

/-- Consequence: the weighted coefficient sum grows no faster than k^3. -/
theorem betaFam_sum_bound (betaFam : ℕ → ℝ) (S : ℝ)
    (hcert : CoeffSumCertified betaFam S) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), |betaFam j| * (3:ℝ) ^ j
      ≤ (Nat.choose (k + 3) 3 : ℝ) * S :=
  coeffSum_bound betaFam k S (hcert k)

/-- The two tail sums of PROOF.md 5.1's unquantified "(lower order)", now
certified: S0 <= 44.5987 (odd-proof/numerics/s0_recursion.py head +
s0_cauchy.py tail, first-order pole) and S1 <= 486.1945 (s1_recursion.py head
453.0838 + s1_cauchy.py tail 33.1107, second-order pole).  An earlier note here
gave S1 <= 453.1, which was the head alone. -/
structure OddTailFacts (bHatOdd : ℕ → ℂ) (S0 S1 : ℝ) : Prop where
  S0_nonneg : 0 ≤ S0
  S1_nonneg : 0 ≤ S1
  /-- The tail's coefficient family is B = d_s H_o + 2 gamma H_o, whose weighted
  norm is S1 + 4 gamma S0.  Nonnegativity is carried as a field because Mathlib
  has no usable lower bound for gamma (cf. `gamma_lower_bound`, which
  supplies one). -/
  Bnorm_nonneg : 0 ≤ S1 + 4 * Real.eulerMascheroniConstant * S0
  tail_h : ∀ k : ℕ, |∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0)|
    ≤ S0 / 2 * ((1:ℝ)/3) ^ k
  -- The coefficient family here is B(z) = d_s H_o(1,z) + 2 gamma H_o(1,z),
  -- so its weighted norm is S1 + 4 gamma S0 (<= 590 for the certified values),
  -- NOT S1 alone.  With |B_j| <= 590 (j+1) 3^-j and
  -- sum_{j>k}(j+1)(2/3)^j = 3(k+4)(2/3)^(k+1), the tail is 2*590*(k+4)(2/3)^k.
  tail_b : ∀ k : ℕ, |∑' j : ℕ, (if k < j then
      ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j
      else 0)|
    ≤ 2 * (S1 + 4 * Real.eulerMascheroniConstant * S0) * ((k:ℝ) + 4)
        * ((2:ℝ)/3) ^ k

/-- The certified dominating sequence.  All three of |h_j(1)|, |b_j| and
betaFam j are bounded by dom j, and CoeffSumCertified dom S holds.  These are
exactly the r = 0, 1, 2 columns that odd-proof/numerics/hcoeff_recursion.py prints,
so the Lean interface and the numerics agree by construction.

A single sequence is needed because the four error pieces of the split draw on
all three: piece (1) on betaFam, (2) and (3) on |b_j|, (4) on |h_j(1)|.  Note
OddCoeffFacts alone bounds none of |h_j(1)| -- tendsto_one gives convergence,
not size -- so this is a genuine additional input, not a repackaging. -/
structure OddDomFacts (dom : ℕ → ℝ) (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (S : ℝ) : Prop where
  dom_nonneg : ∀ j, 0 ≤ dom j
  dom_h      : ∀ j, ‖hCoeff 1 j‖ ≤ dom j
  dom_b      : ∀ j, ‖bHatOdd j‖ ≤ dom j
  dom_beta   : ∀ j, betaFam j ≤ dom j
  dom_cert   : CoeffSumCertified dom S

/-- The weighted sum of the dominating sequence, from step 3. -/
theorem dom_sum_bound (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hd : OddDomFacts dom betaFam bHatOdd S) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), |dom j| * (3:ℝ) ^ j
      ≤ (Nat.choose (k + 3) 3 : ℝ) * S :=
  coeffSum_bound dom k S (hd.dom_cert k)

/-- eps(u) J(u) = e^-2u + O(e^-3u).

Only the FIRST-order expansions are needed: writing

    eps J - e^-2u = (eps - e^-u) J + e^-u (J - e^-u),

each bracket is O(e^-2u) against a factor that is O(e^-u).  This supplies the
b_j e^-2u of MAIN2 and leaves an O(e^-3u) error. -/
theorem eps_jacobian_product :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |(sOf u - 1) * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - Real.exp (-2 * u)|
      ≤ C * Real.exp (-3 * u) := by
  obtain ⟨Ce, hCe, Ue, hUe, he⟩ := eps_of_u_expansion
  obtain ⟨Cj, hCj, Uj, hUj, hj⟩ := jacobian_u_form
  refine ⟨Ce * (Cj + 1) + Cj, by positivity, max Ue Uj, by positivity, ?_⟩
  intro u hu
  have hUe' : Ue ≤ u := le_trans (le_max_left _ _) hu
  have hUj' : Uj ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0:ℝ) ≤ u := le_trans (le_of_lt hUe) hUe'
  set eps := sOf u - 1 with hepsdef
  set J := (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)) with hJdef
  have hE : |eps - Real.exp (-u)| ≤ Ce * Real.exp (-2 * u) := he u hUe'
  have hJd : |J - Real.exp (-u)| ≤ Cj * Real.exp (-2 * u) := hj u hUj'
  have h1 : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  have h2 : (0:ℝ) < Real.exp (-2 * u) := Real.exp_pos _
  have e21 : Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  have e31 : Real.exp (-3 * u) = Real.exp (-u) * Real.exp (-2 * u) := by
    rw [← Real.exp_add]; ring_nf
  have e42 : Real.exp (-2 * u) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr; linarith
  have hJb : |J| ≤ Cj * Real.exp (-2 * u) + Real.exp (-u) := by
    have hd := abs_le.mp hJd
    rw [abs_le]
    constructor
    · linarith [hd.1, h1, h2, hCj]
    · linarith [hd.2, h1]
  have hsplit : eps * J - Real.exp (-2 * u)
      = (eps - Real.exp (-u)) * J + Real.exp (-u) * (J - Real.exp (-u)) := by
    rw [e21]; ring
  rw [hsplit]
  calc |(eps - Real.exp (-u)) * J + Real.exp (-u) * (J - Real.exp (-u))|
      ≤ |(eps - Real.exp (-u)) * J| + |Real.exp (-u) * (J - Real.exp (-u))| :=
        abs_add_le _ _
    _ = |eps - Real.exp (-u)| * |J| + Real.exp (-u) * |J - Real.exp (-u)| := by
        rw [abs_mul, abs_mul, abs_of_pos h1]
    _ ≤ (Ce * Real.exp (-2 * u)) * (Cj * Real.exp (-2 * u) + Real.exp (-u))
          + Real.exp (-u) * (Cj * Real.exp (-2 * u)) := by
        apply add_le_add
        · exact mul_le_mul hE hJb (abs_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left hJd (le_of_lt h1)
    _ ≤ (Ce * (Cj + 1) + Cj) * Real.exp (-3 * u) := by
        rw [e31]
        -- RHS - LHS = Ce Cj e2 (e1 - e2) >= 0
        nlinarith [mul_nonneg (mul_nonneg (le_of_lt hCe) (le_of_lt hCj))
          (mul_nonneg (le_of_lt h2) (sub_nonneg.mpr e42))]

set_option maxHeartbeats 1000000 in
/-- The per-j error bound behind LEAF 1.

Writing h = h_j(1), b = b_j, eps = eps(u), J = J(u) and R_j for the Lagrange
remainder of hCoeff_taylor,

    (h_j(s(u))).re J - h.re e^-u - (b.re + 2g h.re) e^-2u
      = h.re (J - e^-u - 2g e^-2u)     -- jacobian_u_signed
      + b.re (eps J - e^-2u)           -- eps_jacobian_product
      + (R_j).re J                     -- hCoeff_taylor, |R_j| <= beta eps^2/2

each O(e^-3u), with coefficients |h|, |b|, betaFam j -- all bounded by dom j. -/
theorem oddTerm_bound (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hd : OddDomFacts dom betaFam bHatOdd S) :
    ∃ CT > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u → ∀ j : ℕ,
      |(hCoeff (sOf u) j).re
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - (hCoeff 1 j).re * Real.exp (-u)
        - ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
            * Real.exp (-2 * u)|
      ≤ CT * dom j * Real.exp (-3 * u) := by
  obtain ⟨CJ, hCJ, UJ, hUJ, hJsig⟩ := jacobian_u_signed
  obtain ⟨CP, hCP, UP, hUP, hProd⟩ := eps_jacobian_product
  obtain ⟨Cb, hCb, Ub, hUb, hEps⟩ := eps_of_u_bound
  obtain ⟨Cf, hCf, Uf, hUf, hJf⟩ := jacobian_u_form
  -- need sOf u < 2 as well, so that hCoeff_taylor applies
  have hUlt : ∃ U2 > 0, ∀ u : ℝ, U2 ≤ u → sOf u < 2 := by
    -- eps <= Cb e^-u, so sOf u <= 1 + Cb e^-u < 2 once Cb e^-u < 1
    refine ⟨max Ub (Real.log (Cb + 1) + 1), by positivity, ?_⟩
    intro u hu
    have hUb2 : Ub ≤ u := le_trans (le_max_left _ _) hu
    have hlog : Real.log (Cb + 1) + 1 ≤ u := le_trans (le_max_right _ _) hu
    have hb := hEps u hUb2
    have hexp : Cb * Real.exp (-u) < 1 := by
      have h1 : Real.exp (-u) ≤ Real.exp (-(Real.log (Cb + 1) + 1)) := by
        apply Real.exp_le_exp.mpr; linarith
      have h2 : Real.exp (-(Real.log (Cb + 1) + 1))
          = 1 / ((Cb + 1) * Real.exp 1) := by
        rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
          Real.exp_log (by linarith)]
        field_simp
      rw [h2] at h1
      have he1 : (2:ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
        linarith
      have hCbpos : (0:ℝ) < Cb + 1 := by linarith
      calc Cb * Real.exp (-u) ≤ Cb * (1 / ((Cb + 1) * Real.exp 1)) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hCb)
        _ < 1 := by
            rw [mul_one_div, div_lt_one (by positivity)]
            nlinarith [hCb, he1]
    linarith [hb, hexp]
  obtain ⟨U2, hU2, hlt2⟩ := hUlt
  refine ⟨CJ + CP + Cb ^ 2 * (Cf + 1), by positivity,
    max (max UJ UP) (max (max Ub Uf) U2), by positivity, ?_⟩
  intro u hu j
  have hUJ' : UJ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hUP' : UP ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hUb' : Ub ≤ u := by
    refine le_trans ?_ hu
    exact le_trans (le_max_left Ub Uf) (le_trans (le_max_left (max Ub Uf) U2)
      (le_max_right (max UJ UP) (max (max Ub Uf) U2)))
  have hUf' : Uf ≤ u := by
    refine le_trans ?_ hu
    exact le_trans (le_max_right Ub Uf) (le_trans (le_max_left (max Ub Uf) U2)
      (le_max_right (max UJ UP) (max (max Ub Uf) U2)))
  have hU2' : U2 ≤ u := by
    refine le_trans ?_ hu
    exact le_trans (le_max_right (max Ub Uf) U2)
      (le_max_right (max UJ UP) (max (max Ub Uf) U2))
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU2 hU2'
  have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
  have hsmem : sOf u ∈ Set.Ioo (1:ℝ) 2 := ⟨hs1, hlt2 u hU2'⟩
  set eps := sOf u - 1 with hepsdef
  set J := (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)) with hJdef
  -- Taylor: h_s = h + eps b + R, |R| <= betaFam j eps^2 / 2
  have hTay := hCoeff_taylor betaFam bHatOdd hf j (sOf u) hsmem
  set R := hCoeff (sOf u) j - hCoeff 1 j - ((eps : ℝ) : ℂ) * bHatOdd j with hRdef
  have hRb : ‖R‖ ≤ betaFam j * eps ^ 2 / 2 := hTay
  -- the three-way split
  have hsplit : (hCoeff (sOf u) j).re * J
      - (hCoeff 1 j).re * Real.exp (-u)
      - ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
          * Real.exp (-2 * u)
      = (hCoeff 1 j).re * (J - Real.exp (-u)
            - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u))
        + (bHatOdd j).re * (eps * J - Real.exp (-2 * u))
        + R.re * J := by
    have hre : (hCoeff (sOf u) j).re
        = (hCoeff 1 j).re + eps * (bHatOdd j).re + R.re := by
      rw [hRdef]
      simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    ring
  rw [hsplit]
  have hJsig' := hJsig u hUJ'
  have hProd' := hProd u hUP'
  have hepsb := hEps u hUb'
  have hJf' := hJf u hUf'
  have h1 : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  have h2 : (0:ℝ) < Real.exp (-2 * u) := Real.exp_pos _
  have h3 : (0:ℝ) < Real.exp (-3 * u) := Real.exp_pos _
  have hepspos : (0:ℝ) < eps := by
    rw [hepsdef]; linarith [hs1]
  -- |J| <= (Cf + 1) e^-u
  have hJbound : |J| ≤ (Cf + 1) * Real.exp (-u) := by
    have hd := abs_le.mp hJf'
    have he2 : Real.exp (-2 * u) ≤ Real.exp (-u) := by
      apply Real.exp_le_exp.mpr; linarith [hu0]
    rw [abs_le]
    constructor
    · nlinarith [hd.1, h1, h2, hCf, he2]
    · nlinarith [hd.2, h1, h2, hCf, he2]
  -- |R| <= betaFam j Cb^2 e^-2u / 2
  have hRbound : ‖R‖ ≤ betaFam j * Cb ^ 2 * Real.exp (-2 * u) / 2 := by
    refine le_trans hRb ?_
    have hsq : eps ^ 2 ≤ (Cb * Real.exp (-u)) ^ 2 := by
      nlinarith [hepsb, hepspos]
    have hexpand : (Cb * Real.exp (-u)) ^ 2 = Cb ^ 2 * Real.exp (-2 * u) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [hexpand] at hsq
    have hbn := hd.dom_beta j
    have hbnn : 0 ≤ betaFam j := hf.nonneg j
    nlinarith [hsq, hbnn]
  have hReR : |R.re| ≤ ‖R‖ := by
    first
    | exact Complex.abs_re_le_norm R
    | exact Complex.abs_re_le_abs R
    | exact_mod_cast Complex.abs_re_le_abs R
  have hReh : |(hCoeff 1 j).re| ≤ dom j := by
    refine le_trans ?_ (hd.dom_h j)
    first
    | exact Complex.abs_re_le_norm _
    | exact Complex.abs_re_le_abs _
  have hReb : |(bHatOdd j).re| ≤ dom j := by
    refine le_trans ?_ (hd.dom_b j)
    first
    | exact Complex.abs_re_le_norm _
    | exact Complex.abs_re_le_abs _
  have hbeta : betaFam j ≤ dom j := hd.dom_beta j
  calc |(hCoeff 1 j).re * (J - Real.exp (-u)
          - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u))
        + (bHatOdd j).re * (eps * J - Real.exp (-2 * u)) + R.re * J|
      ≤ |(hCoeff 1 j).re * (J - Real.exp (-u)
            - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u))
          + (bHatOdd j).re * (eps * J - Real.exp (-2 * u))| + |R.re * J| :=
        abs_add_le _ _
    _ ≤ |(hCoeff 1 j).re| * |J - Real.exp (-u)
            - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u)|
        + |(bHatOdd j).re| * |eps * J - Real.exp (-2 * u)|
        + |R.re| * |J| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        linarith [abs_add_le ((hCoeff 1 j).re * (J - Real.exp (-u)
          - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u)))
          ((bHatOdd j).re * (eps * J - Real.exp (-2 * u)))]
    _ ≤ (CJ + CP + Cb ^ 2 * (Cf + 1)) * dom j * Real.exp (-3 * u) := by
        have hdn : 0 ≤ dom j := hd.dom_nonneg j
        have hbnn : 0 ≤ betaFam j := hf.nonneg j
        -- term 1
        have t1 : |(hCoeff 1 j).re| * |J - Real.exp (-u)
              - 2 * Real.eulerMascheroniConstant * Real.exp (-2 * u)|
            ≤ dom j * (CJ * Real.exp (-3 * u)) :=
          mul_le_mul hReh hJsig' (abs_nonneg _) hdn
        -- term 2
        have t2 : |(bHatOdd j).re| * |eps * J - Real.exp (-2 * u)|
            ≤ dom j * (CP * Real.exp (-3 * u)) :=
          mul_le_mul hReb hProd' (abs_nonneg _) hdn
        -- term 3
        have t3 : |R.re| * |J|
            ≤ (betaFam j * Cb ^ 2 * Real.exp (-2 * u) / 2)
              * ((Cf + 1) * Real.exp (-u)) := by
          apply mul_le_mul (le_trans hReR hRbound) hJbound (abs_nonneg _)
          positivity
        have hexp23 : Real.exp (-2 * u) * Real.exp (-u) = Real.exp (-3 * u) := by
          rw [← Real.exp_add]; ring_nf
        have t3' : (betaFam j * Cb ^ 2 * Real.exp (-2 * u) / 2)
              * ((Cf + 1) * Real.exp (-u))
            ≤ dom j * (Cb ^ 2 * (Cf + 1) * Real.exp (-3 * u)) := by
          have hkey : (betaFam j * Cb ^ 2 * Real.exp (-2 * u) / 2)
                * ((Cf + 1) * Real.exp (-u))
              = betaFam j * (Cb ^ 2 * (Cf + 1)) / 2
                * (Real.exp (-2 * u) * Real.exp (-u)) := by ring
          rw [hkey, hexp23]
          have hcoef : betaFam j * (Cb ^ 2 * (Cf + 1)) / 2
              ≤ dom j * (Cb ^ 2 * (Cf + 1)) := by
            have hX : (0:ℝ) < Cb ^ 2 * (Cf + 1) := by positivity
            have hmul := mul_le_mul_of_nonneg_right hbeta (le_of_lt hX)
            nlinarith [hmul, hbnn, hX]
          calc betaFam j * (Cb ^ 2 * (Cf + 1)) / 2 * Real.exp (-3 * u)
              ≤ dom j * (Cb ^ 2 * (Cf + 1)) * Real.exp (-3 * u) :=
                mul_le_mul_of_nonneg_right hcoef (le_of_lt h3)
            _ = dom j * (Cb ^ 2 * (Cf + 1) * Real.exp (-3 * u)) := by ring
        linarith [t1, t2, t3, t3']

/-- LEAF 1: the pointwise split of the integrand on Ici U.

    integrand = MAIN1 + MAIN2 + ERR,   |ERR| <= 4 W_k(u) e^-3u

where W_k(u) = sum_{j<=k} dom j u^(k-j)/(k-j)! collects the coefficient
weights.  The four pieces are (1) the Lagrange remainder against J, (2) eps b_j
against J - e^-u, (3) (eps - e^-u) b_j against e^-u, and (4) h_j(1) against
J - e^-u - 2 gamma e^-2u. -/
theorem oddIntegrand_split (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hd : OddDomFacts dom betaFam bHatOdd S) (k : ℕ) :
    ∃ CE > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |(∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u|
      ≤ CE * (∑ j ∈ Finset.range (k + 1),
          dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u) := by
  obtain ⟨CT, hCT, U, hU, hterm⟩ := oddTerm_bound dom betaFam bHatOdd S hf hd
  refine ⟨CT, hCT, U, hU, ?_⟩
  intro u hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hU hu
  set J := (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)) with hJdef
  have hwnn : ∀ j : ℕ, (0:ℝ) ≤ u ^ (k - j) / (Nat.factorial (k - j)) := by
    intro j; positivity
  -- pull the weights out of the difference, then bound termwise
  have hdiff : (∑ j ∈ Finset.range (k + 1), (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j))) * J
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u
      = ∑ j ∈ Finset.range (k + 1),
          ((hCoeff (sOf u) j).re * J
            - (hCoeff 1 j).re * Real.exp (-u)
            - ((bHatOdd j).re
                + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
              * Real.exp (-2 * u)) * (u ^ (k - j) / (Nat.factorial (k - j))) := by
    unfold oddSplitMain1 oddSplitMain2
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdiff]
  calc |∑ j ∈ Finset.range (k + 1),
          ((hCoeff (sOf u) j).re * J
            - (hCoeff 1 j).re * Real.exp (-u)
            - ((bHatOdd j).re
                + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
              * Real.exp (-2 * u)) * (u ^ (k - j) / (Nat.factorial (k - j)))|
      ≤ ∑ j ∈ Finset.range (k + 1),
          |((hCoeff (sOf u) j).re * J
            - (hCoeff 1 j).re * Real.exp (-u)
            - ((bHatOdd j).re
                + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
              * Real.exp (-2 * u)) * (u ^ (k - j) / (Nat.factorial (k - j)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1),
          (CT * dom j * Real.exp (-3 * u)) * (u ^ (k - j) / (Nat.factorial (k - j))) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hwnn j)]
        exact mul_le_mul_of_nonneg_right (hterm u hu j) (hwnn j)
    _ = CT * (∑ j ∈ Finset.range (k + 1), dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- LEAF 2: the error integrates to O(k^3 3^-k), via gamma_normalised_three
and step 3's coefficient bound. -/
theorem oddErr_integral_bound (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (S CE : ℝ) (hCE : 0 ≤ CE)
    (hd : OddDomFacts dom betaFam bHatOdd S) (k : ℕ) :
    CE * ∫ u in Set.Ioi (0:ℝ),
        (∑ j ∈ Finset.range (k + 1),
          dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u)
      ≤ CE * (Nat.choose (k + 3) 3 : ℝ) * S * ((1:ℝ)/3) ^ (k + 1) := by
  have hrw : ∀ u : ℝ,
      (∑ j ∈ Finset.range (k + 1),
        dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u)
      = ∑ j ∈ Finset.range (k + 1),
        (dom j / (Nat.factorial (k - j)) * (u ^ (k - j) * Real.exp (-(3 * u)))) := by
    intro u
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have h3u : (-3 : ℝ) * u = -(3 * u) := by ring
    rw [h3u]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => hrw u)]
  rw [MeasureTheory.integral_finsetSum]
  · -- each term integrates to dom j * 3^-(k-j+1)
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (∫ u in Set.Ioi (0:ℝ),
          dom j / (Nat.factorial (k - j)) * (u ^ (k - j) * Real.exp (-(3 * u))))
        = dom j * ((1:ℝ)/3) ^ (k + 1) * (3:ℝ) ^ j := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [MeasureTheory.integral_const_mul]
      have hg := gamma_normalised_three (k - j)
      rw [div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero (k - j))] at hg
      rw [hg]
      -- 3^-(k-j+1) = 3^-(k+1) * 3^j, since (k-j+1) + j = k+1
      have hexp : j + (k - j + 1) = k + 1 := by omega
      have hfne : ((Nat.factorial (k - j) : ℝ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (k - j)
      have h3a : ((3:ℝ) ^ (k - j + 1)) ≠ 0 := by positivity
      -- put both sides over the same basis: 3^(k+1) = 3^j * 3^(k-j+1)
      rw [div_pow, one_pow, show k + 1 = j + (k - j + 1) from hexp.symm, pow_add]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm]
    -- sum_j dom j (1/3)^(k+1) 3^j = (1/3)^(k+1) sum_j dom j 3^j
    have hfac : ∑ j ∈ Finset.range (k + 1), dom j * ((1:ℝ)/3) ^ (k + 1) * (3:ℝ) ^ j
        = ((1:ℝ)/3) ^ (k + 1) * ∑ j ∈ Finset.range (k + 1), dom j * (3:ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfac]
    have habs : ∑ j ∈ Finset.range (k + 1), dom j * (3:ℝ) ^ j
        ≤ (Nat.choose (k + 3) 3 : ℝ) * S := by
      have := dom_sum_bound dom betaFam bHatOdd S hd k
      refine le_trans (Finset.sum_le_sum ?_) this
      intro j _
      have : dom j ≤ |dom j| := le_abs_self _
      have h3 : (0:ℝ) ≤ (3:ℝ) ^ j := by positivity
      exact mul_le_mul_of_nonneg_right this h3
    have h13 : (0:ℝ) ≤ ((1:ℝ)/3) ^ (k + 1) := by positivity
    calc CE * (((1:ℝ)/3) ^ (k + 1)
            * ∑ j ∈ Finset.range (k + 1), dom j * (3:ℝ) ^ j)
        ≤ CE * (((1:ℝ)/3) ^ (k + 1) * ((Nat.choose (k + 3) 3 : ℝ) * S)) := by
          apply mul_le_mul_of_nonneg_left _ hCE
          exact mul_le_mul_of_nonneg_left habs h13
      _ = CE * (Nat.choose (k + 3) 3 : ℝ) * S * ((1:ℝ)/3) ^ (k + 1) := by ring
  · -- integrability of each term
    intro j _
    have hgam : MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-x) * x ^ (((k - j : ℕ) : ℝ) + 1 - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (by positivity)
    simp only [add_sub_cancel_right] at hgam
    have hgam' : MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ ((k - j : ℕ)) * Real.exp (-x)) (Set.Ioi 0) := by
      apply hgam.congr_fun _ measurableSet_Ioi
      intro x _
      simp only
      rw [← Real.rpow_natCast x (k - j)]
      ring
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.mono hgam'
    · apply MeasureTheory.AEStronglyMeasurable.mul <;>
        (apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0:ℝ) < x := hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos (-(3*x))), abs_of_pos (Real.exp_pos (-x))]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      linarith

/-! ### LEAF 3, rerouted: the near piece in the s-variable

On Ioc 0 U the u-substitution is hostile -- s(u) is LARGE there, the Jacobian
blows up like 2^s, and neither hCoeff_lipschitz nor hCoeff_sub_one_bound
applies (both need s in Ioo 1 2).  But fOdd_eq_integral_FkOdd lets us stay in
s: the near piece is s >= S0 = sOf U, and there the elementary bound

    n >= 3^k  for every n with Omega(n) = k and all factors odd

does the work with no coefficient machinery at all. -/

/-- Every odd n with Omega(n) = k is at least 3^k. -/
theorem FkOdd_ge_three_pow (k : ℕ)
    (n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}) :
    (3:ℝ) ^ k ≤ (n : ℕ) := by
  obtain ⟨m, hm3, hmodd, hmk⟩ := n
  simp only
  have hm0 : m ≠ 0 := by omega
  have heq : m = m.factorization.prod (fun p e => p ^ e) :=
    (Nat.factorization_prod_pow_eq_self hm0).symm
  have hodd3 : ∀ p ∈ m.factorization.support, 3 ≤ p := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    have hpp := hp.1
    have hpdvd := hp.2.1
    have hp2 : p ≠ 2 := by
      intro h; apply hmodd; rw [← h]; exact hpdvd
    have hple2 := hpp.two_le
    omega
  have hcast : (m : ℝ) = ∏ p ∈ m.factorization.support, (p:ℝ) ^ (m.factorization p) := by
    conv_lhs => rw [heq]
    rw [Finsupp.prod]
    push_cast
    rfl
  rw [hcast]
  have hbigOmega : bigOmega m = ∑ p ∈ m.factorization.support, m.factorization p := by
    unfold bigOmega
    rw [Finsupp.sum]
  rw [hmk] at hbigOmega
  calc (3:ℝ) ^ k = (3:ℝ) ^ (∑ p ∈ m.factorization.support, m.factorization p) := by
        rw [hbigOmega]
    _ = ∏ p ∈ m.factorization.support, (3:ℝ) ^ (m.factorization p) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p ∈ m.factorization.support, (p:ℝ) ^ (m.factorization p) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p hp
          first
          | exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hodd3 p hp) _
          | exact pow_le_pow_left (by norm_num) (by exact_mod_cast hodd3 p hp) _

/-- The far-s tail: for s >= S0 > 1,

    FkOdd k s <= 3^(-k(s - S0)) FkOdd k S0,

since every term satisfies n^-s = n^-S0 n^-(s-S0) <= n^-S0 (3^k)^-(s-S0). -/
theorem FkOdd_tail_ratio (k : ℕ) (S0 s : ℝ) (hS0 : 1 < S0) (hs : S0 ≤ s) :
    FkOdd k s ≤ (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0 := by
  unfold FkOdd
  have hSs : Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      (n:ℝ) ^ (-s)) := FkOdd_summable k s (by linarith)
  have hSS0 : Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * (n:ℝ) ^ (-S0)) :=
    (FkOdd_summable k S0 hS0).mul_left _
  rw [← tsum_mul_left]
  have hle : ∀ n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k},
      ((n:ℕ):ℝ) ^ (-s) ≤ (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * ((n:ℕ):ℝ) ^ (-S0) := by
    intro n
    have hn0 : (0:ℝ) < (n:ℕ) := by
      have := n.2.1; positivity
    have hn3k : (3:ℝ) ^ (k:ℝ) ≤ (n:ℕ) := by
      have h3k := FkOdd_ge_three_pow k n
      rwa [Real.rpow_natCast]
    have hsplit : ((n:ℕ):ℝ) ^ (-s) = ((n:ℕ):ℝ) ^ (-S0) * ((n:ℕ):ℝ) ^ (-(s - S0)) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    rw [hsplit]
    have hpk0 : (0:ℝ) < (3:ℝ) ^ (k:ℝ) := by positivity
    have hmono : ((n:ℕ):ℝ) ^ (-(s - S0)) ≤ ((3:ℝ) ^ (k:ℝ)) ^ (-(s - S0)) := by
      apply Real.rpow_le_rpow_of_nonpos hpk0 hn3k
      linarith
    have hpow3 : ((3:ℝ) ^ (k:ℝ)) ^ (-(s - S0)) = (3:ℝ) ^ (-(k:ℝ) * (s - S0)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1
      ring
    rw [hpow3] at hmono
    calc ((n:ℕ):ℝ) ^ (-S0) * ((n:ℕ):ℝ) ^ (-(s - S0))
        ≤ ((n:ℕ):ℝ) ^ (-S0) * (3:ℝ) ^ (-(k:ℝ) * (s - S0)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * ((n:ℕ):ℝ) ^ (-S0) := by ring
  first
  | exact Summable.tsum_le_tsum hle hSs hSS0
  | exact tsum_le_tsum hle hSs hSS0

/-- LEAF 3: the near piece is O(3^-k), far inside the C(k+3)^3 3^-k budget. -/
theorem oddNear_s_bound (k : ℕ) (S0 : ℝ) (hS0 : 1 < S0) (hk : 1 ≤ k) :
    MeasureTheory.IntegrableOn (fun s : ℝ => FkOdd k s) (Set.Ioi S0) ∧
    |∫ s in Set.Ioi S0, FkOdd k s|
      ≤ FkOdd k S0 / ((k:ℝ) * Real.log 3) := by
  have hknn : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hFnn : ∀ s : ℝ, 1 < s → 0 ≤ FkOdd k s := by
    intro s hs
    unfold FkOdd
    apply tsum_nonneg
    intro n; positivity
  have hFS0 : 0 ≤ FkOdd k S0 := hFnn S0 hS0
  have hc : (0:ℝ) < (k:ℝ) * Real.log 3 := by positivity
  have hexpS0 : ∫ s in Set.Ioi S0, (3:ℝ) ^ (-(k:ℝ) * (s - S0))
      = ((k:ℝ) * Real.log 3)⁻¹ := by
    have heq : ∀ s : ℝ, (3:ℝ) ^ (-(k:ℝ) * (s - S0))
        = Real.exp (-((k:ℝ) * Real.log 3) * (s - S0)) := by
      intro s
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
      congr 1; ring
    simp_rw [heq]
    have hstep1 : ∫ s in Set.Ioi S0, Real.exp (-((k:ℝ) * Real.log 3) * (s - S0))
        = ∫ s in Set.Ioi S0, Real.exp (-(((k:ℝ) * Real.log 3) * s)
            + ((k:ℝ) * Real.log 3) * S0) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro s _
      congr 1
      ring
    have hstep2 : ∫ s in Set.Ioi S0, Real.exp (-(((k:ℝ) * Real.log 3) * s)
          + ((k:ℝ) * Real.log 3) * S0)
        = Real.exp (((k:ℝ) * Real.log 3) * S0)
          * ∫ s in Set.Ioi S0, Real.exp (-(((k:ℝ) * Real.log 3) * s)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro s _
      show Real.exp (-(((k:ℝ) * Real.log 3) * s) + ((k:ℝ) * Real.log 3) * S0)
        = Real.exp (((k:ℝ) * Real.log 3) * S0) * Real.exp (-(((k:ℝ) * Real.log 3) * s))
      rw [← Real.exp_add]
      ring_nf
    have hstep3 : ∫ s in Set.Ioi S0, Real.exp (-(((k:ℝ) * Real.log 3) * s))
        = ((k:ℝ) * Real.log 3)⁻¹
          * ∫ x in Set.Ioi (((k:ℝ) * Real.log 3) * S0), Real.exp (-x) := by
      have h := MeasureTheory.integral_comp_mul_left_Ioi
        (fun x : ℝ => Real.exp (-x)) S0 hc
      simpa using h
    have hstep4 : ∫ x in Set.Ioi (((k:ℝ) * Real.log 3) * S0), Real.exp (-x)
        = Real.exp (-(((k:ℝ) * Real.log 3) * S0)) :=
      integral_exp_neg_Ioi _
    rw [hstep1, hstep2, hstep3, hstep4]
    have hcombine : Real.exp ((k:ℝ) * Real.log 3 * S0)
          * (((k:ℝ) * Real.log 3)⁻¹
            * Real.exp (-((k:ℝ) * Real.log 3 * S0)))
        = ((k:ℝ) * Real.log 3)⁻¹
          * (Real.exp ((k:ℝ) * Real.log 3 * S0)
            * Real.exp (-((k:ℝ) * Real.log 3 * S0))) := by ring
    rw [hcombine, ← Real.exp_add]
    have hzero : (k:ℝ) * Real.log 3 * S0 + -((k:ℝ) * Real.log 3 * S0) = 0 := by ring
    rw [hzero, Real.exp_zero, mul_one]
  have hgint : ∫ s in Set.Ioi S0, (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0
      = FkOdd k S0 / ((k:ℝ) * Real.log 3) := by
    rw [MeasureTheory.integral_mul_const, hexpS0]
    field_simp
  have hmaj : ∀ s ∈ Set.Ioi S0, |FkOdd k s|
      ≤ (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0 := by
    intro s hs
    rw [abs_of_nonneg (hFnn s (by have := Set.mem_Ioi.mp hs; linarith))]
    exact FkOdd_tail_ratio k S0 s hS0 (le_of_lt (Set.mem_Ioi.mp hs))
  have hmajBare : ∀ s ∈ Set.Ioi S0, FkOdd k s
      ≤ (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0 := by
    intro s hs
    have h := hmaj s hs
    rwa [abs_of_nonneg (hFnn s (by have := Set.mem_Ioi.mp hs; linarith))] at h
  have hmajint : MeasureTheory.IntegrableOn
      (fun s : ℝ => (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0) (Set.Ioi S0) := by
    have heq : (fun s : ℝ => (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0)
        = (fun s : ℝ => FkOdd k S0 * (Real.exp ((k:ℝ) * Real.log 3 * S0)
            * Real.exp (-((k:ℝ) * Real.log 3 * s)))) := by
      funext s
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), ← Real.exp_add]
      rw [show (k:ℝ) * Real.log 3 * S0 + -((k:ℝ) * Real.log 3 * s)
            = Real.log 3 * (-(k:ℝ) * (s - S0)) from by ring]
      ring
    rw [heq]
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.Integrable.const_mul
    have hb : (0:ℝ) < (k:ℝ) * Real.log 3 := hc
    have h1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-x)) (Set.Ioi (((k:ℝ) * Real.log 3) * S0)) :=
      integrableOn_exp_neg_Ioi _
    exact (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x)) S0 hb).mpr h1
  have hcontF : ContinuousOn (FkOdd k) (Set.Ici S0) := by
    unfold FkOdd
    apply continuousOn_tsum
      (u := fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
        ((n:ℕ):ℝ) ^ (-S0))
      _ (FkOdd_summable k S0 hS0)
    · intro n x hx
      have hxS0 : S0 ≤ x := hx
      have hn0 : (0:ℝ) < (n:ℕ) := by
        have := n.2.1; positivity
      have hn3 : (3:ℝ) ≤ (n:ℕ) := by exact_mod_cast n.2.1
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
      have hn1 : (1:ℝ) ≤ (n:ℕ) := by linarith [hn3]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · intro n
      apply Continuous.continuousOn
      have hn0 : (0:ℝ) < (n:ℕ) := by
        have := n.2.1; positivity
      apply Continuous.rpow continuous_const continuous_neg
      intro x
      left
      exact ne_of_gt hn0
  have hAESM : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => FkOdd k s)
      (MeasureTheory.volume.restrict (Set.Ioi S0)) :=
    (hcontF.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hboundAE : Filter.Eventually
      (fun s : ℝ => ‖FkOdd k s‖ ≤ (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi S0))) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn s (by have := Set.mem_Ioi.mp hs; linarith))]
    exact hmajBare s hs
  have hFint : MeasureTheory.IntegrableOn (fun s : ℝ => FkOdd k s) (Set.Ioi S0) :=
    MeasureTheory.Integrable.mono' hmajint hAESM hboundAE
  refine ⟨hFint, ?_⟩
  calc |∫ s in Set.Ioi S0, FkOdd k s|
      ≤ ∫ s in Set.Ioi S0, (3:ℝ) ^ (-(k:ℝ) * (s - S0)) * FkOdd k S0 := by
        rw [abs_of_nonneg (MeasureTheory.integral_nonneg
          (fun s => by
            by_cases hs : s ∈ Set.Ioi S0
            · exact hFnn s (by have := Set.mem_Ioi.mp hs; linarith)
            · unfold FkOdd
              apply tsum_nonneg
              intro n
              positivity))]
        exact MeasureTheory.setIntegral_mono_on hFint hmajint measurableSet_Ioi hmajBare
    _ = FkOdd k S0 / ((k:ℝ) * Real.log 3) := hgint


/-- sOf is strictly antitone on (0, inf): the inverse of a strictly
antitone bijection is strictly antitone. -/
theorem sOf_strictAntiOn : StrictAntiOn sOf (Set.Ioi 0) := by
  intro u1 hu1 u2 hu2 hu12
  simp only [Set.mem_Ioi] at hu1 hu2
  by_contra hcon
  push_neg at hcon
  have h1 : (1:ℝ) < sOf u1 := sOf_mem u1 hu1
  have h2 : (1:ℝ) < sOf u2 := sOf_mem u2 hu2
  rcases eq_or_lt_of_le hcon with heq | hlt
  · have huEq : u1 = u2 := by
      rw [← uOf_sOf u1 hu1, ← uOf_sOf u2 hu2, heq]
    linarith [hu12, huEq]
  · have hmono := uOf_strictAnti h1 h2 hlt
    rw [uOf_sOf u1 hu1, uOf_sOf u2 hu2] at hmono
    linarith [hu12, hmono]

/-- Restricted change of variables: u in Ioc 0 U corresponds to
s in Ici (sOf U), since sOf is a strictly antitone bijection (0,inf) -> (1,inf)
sending u -> 0+ to s -> inf and u = U to s = sOf U. -/
theorem uOf_change_of_variables_Ioc (U : ℝ) (hU : 0 < U) (g : ℝ → ℝ) :
    (∫ u in Set.Ioc (0:ℝ) U, g u)
      = ∫ s in Set.Ici (sOf U),
          |zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))| * g (uOf s) := by
  have himg : uOf '' (Set.Ici (sOf U)) = Set.Ioc (0:ℝ) U := by
    apply Set.eq_of_subset_of_subset
    · rintro u ⟨s, hs, rfl⟩
      have hsIci : sOf U ≤ s := Set.mem_Ici.mp hs
      have hs1 : (1:ℝ) < s := lt_of_lt_of_le (sOf_mem U hU) hsIci
      refine ⟨?_, ?_⟩
      · have h0mem : uOf '' (Set.Ioi 1) = Set.Ioi 0 := uOf_image
        have : uOf s ∈ Set.Ioi (0:ℝ) := by
          rw [← h0mem]; exact ⟨s, hs1, rfl⟩
        exact this
      · rcases eq_or_lt_of_le hsIci with heq | hlt
        · rw [← heq, uOf_sOf U hU]
        · have hst := uOf_strictAnti (sOf_mem U hU) hs1 hlt
          rw [uOf_sOf U hU] at hst
          exact le_of_lt hst
    · intro u hu
      have hu0 : (0:ℝ) < u := hu.1
      have huU : u ≤ U := hu.2
      refine ⟨sOf u, Set.mem_Ici.mpr ?_, uOf_sOf u hu0⟩
      rcases eq_or_lt_of_le huU with heq | hlt
      · rw [heq]
      · exact le_of_lt (sOf_strictAntiOn (Set.mem_Ioi.mpr hu0) (Set.mem_Ioi.mpr hU) hlt)
  rw [← himg]
  apply MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ici
  · intro s hs
    have hs1 : (1:ℝ) < s := lt_of_lt_of_le (sOf_mem U hU) hs
    exact (uOf_hasDerivAt s hs1).hasDerivWithinAt
  · exact uOf_strictAnti.injOn.mono (fun s hs =>
      lt_of_lt_of_le (sOf_mem U hU) hs)

/-- Restricted substitution in the direction the assembly needs, mirroring
`integral_substitute` but on Ici (sOf U) / Ioc 0 U. -/
theorem integral_substitute_Ioc (U : ℝ) (hU : 0 < U) (F : ℝ → ℝ) :
    (∫ s in Set.Ici (sOf U), F s)
      = ∫ u in Set.Ioc (0:ℝ) U,
          F (sOf u) * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))) := by
  rw [uOf_change_of_variables_Ioc U hU
    (fun u => F (sOf u) * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro s hs
  have hs1 : (1:ℝ) < s := lt_of_lt_of_le (sOf_mem U hU) (Set.mem_Ici.mp hs)
  simp only
  rw [sOf_uOf s hs1]
  -- |u'(s)| = -zeta'(s)/zeta(s), so |u'| * (zeta / (-zeta')) = 1
  have hzpos : (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by
    have hsummable : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-s)) := by
      have hb := Real.summable_nat_rpow.mpr (by linarith : (-s:ℝ) < -1)
      apply ((summable_nat_add_iff 1).mpr hb).congr
      intro n
      push_cast
      ring_nf
    have hle := hsummable.le_tsum 0 (fun n _ => by positivity)
    calc (0:ℝ) < ((0:ℝ) + 1) ^ (-s) := by norm_num
      _ ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) := by simpa using hle
  have hderivneg : zetaRderiv s < 0 := by
    unfold zetaRderiv
    have hsum := log_rpow_summable s hs1
    have hneg : (∑' n : ℕ, (-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-s))
        = -∑' n : ℕ, Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-s) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      ring
    rw [hneg, neg_lt_zero]
    have hterm : (0:ℝ) < Real.log (((1:ℕ):ℝ) + 1) * (((1:ℕ):ℝ) + 1) ^ (-s) := by
      apply mul_pos
      · apply Real.log_pos
        norm_num
      · positivity
    have hle := hsum.le_tsum 1 (fun n _ => by
      apply mul_nonneg _ (by positivity)
      apply Real.log_nonneg
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith)
    linarith
  have habs : |zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s))|
      = -zetaRderiv s / (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) := by
    rw [abs_div, abs_of_pos hzpos, abs_of_neg hderivneg]
  rw [habs]
  have hdne : zetaRderiv s ≠ 0 := ne_of_lt hderivneg
  field_simp

/-- FkOdd at a fixed exponent tau > 1 is bounded by the full zeta sum,
uniformly in k: the index set injects into the naturals. -/
theorem FkOdd_le_zeta (k : ℕ) (tau : ℝ) (htau : 1 < tau) :
    FkOdd k tau ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-tau) := by
  unfold FkOdd
  apply Real.tsum_le_of_sum_le
  · intro n
    positivity
  · intro t
    have hznn : ∀ m : ℕ, (0:ℝ) ≤ ((m:ℝ) + 1) ^ (-tau) := by
      intro m; positivity
    have hzsum : Summable (fun m : ℕ => ((m:ℝ) + 1) ^ (-tau)) := by
      have hb := Real.summable_nat_rpow.mpr (by linarith : (-tau:ℝ) < -1)
      apply ((summable_nat_add_iff 1).mpr hb).congr
      intro m
      push_cast
      ring_nf
    -- map the finset into N by n -> n - 1, then compare with the full sum
    classical
    have hinj : ∀ a ∈ t, ∀ b ∈ t, ((a:ℕ) - 1 : ℕ) = ((b:ℕ) - 1 : ℕ) → a = b := by
      intro a ha b hb hab
      have ha3 : 3 ≤ (a:ℕ) := a.2.1
      have hb3 : 3 ≤ (b:ℕ) := b.2.1
      apply Subtype.ext
      omega
    set g : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} → ℕ :=
      fun x => (x : ℕ) - 1 with hg
    have hstep : ∑ x ∈ t, ((x:ℕ):ℝ) ^ (-tau)
        = ∑ m ∈ Finset.image g t, ((m:ℝ) + 1) ^ (-tau) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro x hx
      have hx3 : 3 ≤ (x:ℕ) := x.2.1
      have hcast : ((g x : ℕ):ℝ) + 1 = ((x:ℕ):ℝ) := by
        rw [hg]
        have h1 : (1:ℕ) ≤ (x:ℕ) := by omega
        push_cast [Nat.cast_sub h1]
        ring
      rw [hcast]
    rw [hstep]
    exact hzsum.sum_le_tsum _ (fun m _ => hznn m)

/-- The near-piece constant: for sigma >= tau > 1, FkOdd k sigma decays like
3^(-k(sigma-tau)) times a k-independent constant. -/
theorem FkOdd_le_pow (k : ℕ) (tau sigma : ℝ) (htau : 1 < tau) (hsig : tau ≤ sigma) :
    FkOdd k sigma ≤ (3:ℝ) ^ (-(k:ℝ) * (sigma - tau)) * (∑' n : ℕ, ((n:ℝ) + 1) ^ (-tau)) := by
  refine le_trans (FkOdd_tail_ratio k tau sigma htau hsig) ?_
  apply mul_le_mul_of_nonneg_left (FkOdd_le_zeta k tau htau)
  positivity

/-- FkOdd k is continuous on Ici S0 for every S0 > 1: the defining tsum
converges uniformly there, dominated by n^(-S0). -/
theorem FkOdd_continuousOn_Ici (k : ℕ) (S0 : ℝ) (hS0 : 1 < S0) :
    ContinuousOn (FkOdd k) (Set.Ici S0) := by
  unfold FkOdd
  apply continuousOn_tsum
    (u := fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      ((n:ℕ):ℝ) ^ (-S0))
    _ (FkOdd_summable k S0 hS0)
  · intro n x hx
    have hxS0 : S0 ≤ x := hx
    have hn0 : (0:ℝ) < (n:ℕ) := by
      have := n.2.1; positivity
    have hn3 : (3:ℝ) ≤ (n:ℕ) := by exact_mod_cast n.2.1
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    have hn1 : (1:ℝ) ≤ (n:ℕ) := by linarith [hn3]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  · intro n
    apply Continuous.continuousOn
    have hn0 : (0:ℝ) < (n:ℕ) := by
      have := n.2.1; positivity
    apply Continuous.rpow continuous_const continuous_neg
    intro x
    left
    exact ne_of_gt hn0

/-- Hence FkOdd k is continuous on all of Ioi 1: every point of Ioi 1 lies in
Ici S0 for some S0 > 1 strictly below it. -/
theorem FkOdd_continuousOn_Ioi (k : ℕ) :
    ContinuousOn (FkOdd k) (Set.Ioi (1:ℝ)) := by
  intro s hs
  have hs1 : (1:ℝ) < s := hs
  set S0 := (1 + s) / 2 with hS0def
  have hS0 : (1:ℝ) < S0 := by rw [hS0def]; linarith
  have hsS0 : S0 < s := by rw [hS0def]; linarith
  have hmem : s ∈ Set.Ici S0 := le_of_lt hsS0
  have hcont := FkOdd_continuousOn_Ici k S0 hS0
  have hsub : Set.Ioi S0 ⊆ Set.Ici S0 := by
    intro x hx
    rw [Set.mem_Ioi] at hx
    rw [Set.mem_Ici]
    exact le_of_lt hx
  have hwithin : ContinuousWithinAt (FkOdd k) (Set.Ioi S0) s :=
    (hcont s hmem).mono hsub
  apply hwithin.mono_of_mem_nhdsWithin
  first
  | exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hsS0)
  | exact nhdsWithin_le_nhds (Ioi_mem_nhds hsS0)
  | exact Filter.mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds hsS0)) (fun _ h => h)

/-- LEAF 3, closed: the near piece is bounded via oddNear_s_bound in the
s-variable, connected by the restricted change of variables above. -/
theorem oddNear_integral_bound (U : ℝ) (hU : 0 < U) (k : ℕ) (hk : 1 ≤ k)
    (hsum : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - zOmegaHom s z (p : ℕ))⁻¹))
    (hcd1 : ∀ s : ℝ, 1 < s →
      ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ∀ s : ℝ, 1 < s → ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0) :
    |∫ u in Set.Ioc (0:ℝ) U,
        (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))|
      ≤ FkOdd k (sOf U) / ((k:ℝ) * Real.log 3) := by
  have hSU : (1:ℝ) < sOf U := sOf_mem U hU
  have hrw : ∀ u ∈ Set.Ioc (0:ℝ) U,
      (∑ j ∈ Finset.range (k + 1),
        (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
      = FkOdd k (sOf u) * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu.1
    have hsu1 : (1:ℝ) < sOf u := sOf_mem u hu0
    have hexp := FkOdd_expansion' k hk (sOf u) hsu1
      (hsum (sOf u) hsu1) (hmul3 (sOf u) hsu1) (hcd1 (sOf u) hsu1) (hcd2 (sOf u) hsu1)
    have huos : uOf (sOf u) = u := uOf_sOf u hu0
    rw [huos] at hexp
    have hre : (FkOdd k (sOf u) : ℝ) = ∑ j ∈ Finset.range (k + 1),
        (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)) := by
      have := congrArg Complex.re hexp
      simp only [Complex.ofReal_re] at this
      rw [this, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hcast : (hCoeff (sOf u) j * (u:ℂ) ^ (k - j) / ((Nat.factorial (k - j) : ℕ) : ℂ))
          = hCoeff (sOf u) j
            * (((u ^ (k - j) / (Nat.factorial (k - j) : ℝ) : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [← hre]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hrw,
    ← integral_substitute_Ioc U hU (fun s => FkOdd k s),
    MeasureTheory.integral_Ici_eq_integral_Ioi]
  exact (oddNear_s_bound k (sOf U) hSU hk).2


/-- MAIN1 over the near interval Ioc 0 U: bounded by the dom-weighted sum
at u = U, times the interval length.  On Ioc 0 U we have exp(-u) <= 1 and
u^(k-j) <= U^(k-j). -/
theorem oddSplitMain1_near (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hd : OddDomFacts dom betaFam bHatOdd S) (U : ℝ) (hU : 0 < U) (k : ℕ) :
    |∫ u in Set.Ioc (0:ℝ) U, oddSplitMain1 k u|
      ≤ U * ∑ j ∈ Finset.range (k + 1),
          dom j * U ^ (k - j) / (Nat.factorial (k - j)) := by
  have hptwise : ∀ u ∈ Set.Ioc (0:ℝ) U, ‖oddSplitMain1 k u‖
      ≤ ∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j)) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu.1
    have huU : u ≤ U := hu.2
    rw [Real.norm_eq_abs, oddSplitMain1, abs_mul,
      abs_of_pos (Real.exp_pos (-u))]
    have hexp1 : Real.exp (-u) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hsum : |∑ j ∈ Finset.range (k + 1),
        (hCoeff 1 j).re * u ^ (k - j) / (Nat.factorial (k - j))|
        ≤ ∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro j _
      have hdj : |(hCoeff 1 j).re| ≤ dom j := by
        refine le_trans ?_ (hd.dom_h j)
        first
        | exact Complex.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
      have hpow : u ^ (k - j) ≤ U ^ (k - j) := by
        first
        | exact pow_le_pow_left₀ (le_of_lt hu0) huU _
        | exact pow_le_pow_left (le_of_lt hu0) huU _
      have hfac : (0:ℝ) < (Nat.factorial (k - j) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (k - j)
      rw [abs_div, abs_mul, abs_of_pos hfac, abs_of_nonneg (pow_nonneg (le_of_lt hu0) _)]
      have hnum : |(hCoeff 1 j).re| * u ^ (k - j) ≤ dom j * U ^ (k - j) :=
        mul_le_mul hdj hpow (pow_nonneg (le_of_lt hu0) _) (hd.dom_nonneg j)
      exact div_le_div_of_nonneg_right hnum (le_of_lt hfac)
    calc |∑ j ∈ Finset.range (k + 1),
            (hCoeff 1 j).re * u ^ (k - j) / (Nat.factorial (k - j))| * Real.exp (-u)
        ≤ (∑ j ∈ Finset.range (k + 1),
            dom j * U ^ (k - j) / (Nat.factorial (k - j))) * 1 :=
          mul_le_mul hsum hexp1 (le_of_lt (Real.exp_pos _)) (by
            apply Finset.sum_nonneg
            intro j _
            have := hd.dom_nonneg j
            positivity)
      _ = _ := by ring
  have hvol : MeasureTheory.volume.real (Set.Ioc (0:ℝ) U) = U := by
    unfold MeasureTheory.Measure.real
    rw [Real.volume_Ioc]
    simp [ENNReal.toReal_ofReal, le_of_lt hU]
  have hfin : MeasureTheory.volume (Set.Ioc (0:ℝ) U) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hptwise
  rw [Real.norm_eq_abs, hvol] at hbound
  linarith [hbound]

/-- MAIN2 over the near interval Ioc 0 U, same shape as MAIN1 but the
coefficient carries the extra 1 + 2 gamma factor. -/
theorem oddSplitMain2_near (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hd : OddDomFacts dom betaFam bHatOdd S) (U : ℝ) (hU : 0 < U) (k : ℕ) :
    |∫ u in Set.Ioc (0:ℝ) U, oddSplitMain2 bHatOdd k u|
      ≤ U * ((1 + 2 * Real.eulerMascheroniConstant)
          * ∑ j ∈ Finset.range (k + 1),
              dom j * U ^ (k - j) / (Nat.factorial (k - j))) := by
  have hg0 : (0:ℝ) < Real.eulerMascheroniConstant := by
    first
    | linarith [Real.one_half_lt_eulerMascheroniConstant]
    | linarith [one_half_lt_eulerMascheroniConstant]
  have hptwise : ∀ u ∈ Set.Ioc (0:ℝ) U, ‖oddSplitMain2 bHatOdd k u‖
      ≤ (1 + 2 * Real.eulerMascheroniConstant)
        * ∑ j ∈ Finset.range (k + 1),
            dom j * U ^ (k - j) / (Nat.factorial (k - j)) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu.1
    have huU : u ≤ U := hu.2
    rw [Real.norm_eq_abs, oddSplitMain2, abs_mul,
      abs_of_pos (Real.exp_pos (-2 * u))]
    have hexp1 : Real.exp (-2 * u) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hsum : |∑ j ∈ Finset.range (k + 1),
        ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
          * u ^ (k - j) / (Nat.factorial (k - j))|
        ≤ (1 + 2 * Real.eulerMascheroniConstant)
          * ∑ j ∈ Finset.range (k + 1),
              dom j * U ^ (k - j) / (Nat.factorial (k - j)) := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro j _
      have hbj : |(bHatOdd j).re| ≤ dom j := by
        refine le_trans ?_ (hd.dom_b j)
        first
        | exact Complex.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
      have hhj : |(hCoeff 1 j).re| ≤ dom j := by
        refine le_trans ?_ (hd.dom_h j)
        first
        | exact Complex.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
      have hcoef : |(bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re|
          ≤ (1 + 2 * Real.eulerMascheroniConstant) * dom j := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.eulerMascheroniConstant)]
        nlinarith [hbj, hhj, hg0, hd.dom_nonneg j]
      have hpow : u ^ (k - j) ≤ U ^ (k - j) := by
        first
        | exact pow_le_pow_left₀ (le_of_lt hu0) huU _
        | exact pow_le_pow_left (le_of_lt hu0) huU _
      have hfac : (0:ℝ) < (Nat.factorial (k - j) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (k - j)
      rw [abs_div, abs_mul, abs_of_pos hfac,
        abs_of_nonneg (pow_nonneg (le_of_lt hu0) _)]
      have hmul : (1 + 2 * Real.eulerMascheroniConstant) * (dom j * U ^ (k - j))
          / (Nat.factorial (k - j) : ℝ)
          = (1 + 2 * Real.eulerMascheroniConstant)
            * (dom j * U ^ (k - j) / (Nat.factorial (k - j))) := by ring
      rw [← hmul]
      have hnn : (0:ℝ) ≤ (1 + 2 * Real.eulerMascheroniConstant) * dom j := by
        nlinarith [hd.dom_nonneg j, hg0]
      have hnum : |(bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re|
            * u ^ (k - j)
          ≤ (1 + 2 * Real.eulerMascheroniConstant) * dom j * U ^ (k - j) :=
        mul_le_mul hcoef hpow (pow_nonneg (le_of_lt hu0) _) hnn
      have hre : (1 + 2 * Real.eulerMascheroniConstant) * dom j * U ^ (k - j)
          = (1 + 2 * Real.eulerMascheroniConstant) * (dom j * U ^ (k - j)) := by ring
      rw [hre] at hnum
      exact div_le_div_of_nonneg_right hnum (le_of_lt hfac)
    calc |∑ j ∈ Finset.range (k + 1),
            ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re)
              * u ^ (k - j) / (Nat.factorial (k - j))| * Real.exp (-2 * u)
        ≤ ((1 + 2 * Real.eulerMascheroniConstant)
            * ∑ j ∈ Finset.range (k + 1),
                dom j * U ^ (k - j) / (Nat.factorial (k - j))) * 1 :=
          mul_le_mul hsum hexp1 (le_of_lt (Real.exp_pos _)) (by
            apply mul_nonneg (by positivity)
            apply Finset.sum_nonneg
            intro j _
            have := hd.dom_nonneg j
            positivity)
      _ = _ := by ring
  have hvol : MeasureTheory.volume.real (Set.Ioc (0:ℝ) U) = U := by
    unfold MeasureTheory.Measure.real
    rw [Real.volume_Ioc]
    simp [ENNReal.toReal_ofReal, le_of_lt hU]
  have hfin : MeasureTheory.volume (Set.Ioc (0:ℝ) U) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hptwise
  rw [Real.norm_eq_abs, hvol] at hbound
  linarith [hbound]

/-- FkOdd k is antitone in s on (1, inf): each term n^(-s) decreases. -/
theorem FkOdd_antitone (k : ℕ) (s t : ℝ) (hs : 1 < s) (hst : s ≤ t) :
    FkOdd k t ≤ FkOdd k s := by
  unfold FkOdd
  have ht : (1:ℝ) < t := lt_of_lt_of_le hs hst
  apply Summable.tsum_le_tsum _ (FkOdd_summable k t ht) (FkOdd_summable k s hs)
  intro n
  have hn1 : (1:ℝ) ≤ ((n:ℕ):ℝ) := by
    have := n.2.1
    have h3 : (3:ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast this
    linarith
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- The dominating sequence decays like a polynomial times 3^-j.

From dom_cert and coeffSum_bound: the weighted partial sums are bounded by
C(m+3,3) S, so each single term satisfies dom j * 3^j <= C(j+3,3) S. -/
theorem dom_decay (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hd : OddDomFacts dom betaFam bHatOdd S) (j : ℕ) :
    dom j * (3:ℝ) ^ j ≤ (Nat.choose (j + 3) 3 : ℝ) * S := by
  have hsum := coeffSum_bound dom j S (hd.dom_cert j)
  have hterm : dom j * (3:ℝ) ^ j
      ≤ ∑ i ∈ Finset.range (j + 1), |dom i| * (3:ℝ) ^ i := by
    have hmem : j ∈ Finset.range (j + 1) := Finset.self_mem_range_succ j
    have hle : dom j * (3:ℝ) ^ j ≤ |dom j| * (3:ℝ) ^ j := by
      apply mul_le_mul_of_nonneg_right (le_abs_self _)
      positivity
    refine le_trans hle
      (Finset.single_le_sum (f := fun i => |dom i| * (3:ℝ) ^ i) ?_ hmem)
    intro i _
    positivity
  exact le_trans hterm hsum

/-- sOf is AEMeasurable on Ioi 0, from strict antitonicity.  Monotone
functions are Borel measurable, so no continuity argument is needed. -/
theorem sOf_aemeasurable :
    AEMeasurable sOf (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
  apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
  exact sOf_strictAntiOn.antitoneOn

/-- zetaRderiv is continuous on Ici S0 for every S0 > 1, by the same
uniform-convergence argument as FkOdd. -/
theorem zetaRderiv_continuousOn_Ici (S0 : ℝ) (hS0 : 1 < S0) :
    ContinuousOn zetaRderiv (Set.Ici S0) := by
  unfold zetaRderiv
  apply continuousOn_tsum
    (u := fun n : ℕ => Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-S0))
    _ (log_rpow_summable S0 hS0)
  · intro n x hx
    have hxS0 : S0 ≤ x := hx
    have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hpos : (0:ℝ) < ((n:ℝ) + 1) ^ (-x) := Real.rpow_pos_of_pos (by positivity) _
    have hlog : (0:ℝ) ≤ Real.log ((n:ℝ) + 1) := Real.log_nonneg hn1
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hlog,
      abs_of_pos hpos]
    apply mul_le_mul_of_nonneg_left _ hlog
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  · intro n
    apply Continuous.continuousOn
    apply Continuous.mul continuous_const
    apply Continuous.rpow continuous_const continuous_neg
    intro x
    left
    have : (0:ℝ) < (n:ℝ) + 1 := by positivity
    exact ne_of_gt this

/-- zetaRderiv is continuous on all of Ioi 1. -/
theorem zetaRderiv_continuousOn_Ioi : ContinuousOn zetaRderiv (Set.Ioi (1:ℝ)) := by
  intro s hs
  have hs1 : (1:ℝ) < s := hs
  set S0 := (1 + s) / 2 with hS0def
  have hS0 : (1:ℝ) < S0 := by rw [hS0def]; linarith
  have hsS0 : S0 < s := by rw [hS0def]; linarith
  have hmem : s ∈ Set.Ici S0 := le_of_lt hsS0
  have hcont := zetaRderiv_continuousOn_Ici S0 hS0
  have hsub : Set.Ioi S0 ⊆ Set.Ici S0 := by
    intro x hx
    rw [Set.mem_Ioi] at hx
    rw [Set.mem_Ici]
    exact le_of_lt hx
  have hwithin : ContinuousWithinAt zetaRderiv (Set.Ioi S0) s :=
    (hcont s hmem).mono hsub
  apply hwithin.mono_of_mem_nhdsWithin
  first
  | exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hsS0)
  | exact nhdsWithin_le_nhds (Ioi_mem_nhds hsS0)


/-- A continuous-on-Ioi-1 function, patched to 0 elsewhere, is globally
measurable; this is the form that composes with sOf. -/
theorem patch_measurable (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (1:ℝ))) :
    Measurable (Set.piecewise (Set.Ioi (1:ℝ)) f (fun _ => 0)) := by
  classical
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : ∃ u : Set ℝ, IsOpen u ∧ f ⁻¹' t ∩ Set.Ioi (1:ℝ)
      = u ∩ Set.Ioi (1:ℝ) := _root_.continuousOn_iff'.1 hf t ht
  rw [Set.piecewise_preimage, Set.ite, hu]
  exact (u_open.measurableSet.inter measurableSet_Ioi).union
    ((measurable_const ht.measurableSet).diff measurableSet_Ioi)

/-- The integrand of fOdd_u_form is AEMeasurable on Ioi 0.

Composition: sOf is AEMeasurable (antitone), FkOdd k is continuous on Ioi 1
and sOf lands there, and the Jacobian is built from zetaR and zetaRderiv,
both continuous on Ioi 1. -/
theorem oddIntegrand_aemeasurable (k : ℕ) :
    AEMeasurable
      (fun u : ℝ => FkOdd k (sOf u)
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
  classical
  set zR : ℝ → ℝ := fun s => ∑' n : ℕ, ((n:ℝ) + 1) ^ (-s) with hzR
  have hzRIci : ∀ S0 : ℝ, 1 < S0 → ContinuousOn zR (Set.Ici S0) := by
    intro S0 hS0
    rw [hzR]
    have hsum : Summable (fun n : ℕ => ((n:ℝ) + 1) ^ (-S0)) := by
      have hb := Real.summable_nat_rpow.mpr (by linarith : (-S0:ℝ) < -1)
      apply ((summable_nat_add_iff 1).mpr hb).congr
      intro n
      push_cast
      ring_nf
    apply continuousOn_tsum
      (u := fun n : ℕ => ((n:ℝ) + 1) ^ (-S0)) _ hsum
    · intro n x hx
      have hxS0 : S0 ≤ x := hx
      have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      have hpos : (0:ℝ) < ((n:ℝ) + 1) ^ (-x) := Real.rpow_pos_of_pos (by positivity) _
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · intro n
      apply Continuous.continuousOn
      apply Continuous.rpow continuous_const continuous_neg
      intro x
      left
      have : (0:ℝ) < (n:ℝ) + 1 := by positivity
      exact ne_of_gt this
  have hzRcont : ContinuousOn zR (Set.Ioi (1:ℝ)) := by
    intro t ht
    have ht1 : (1:ℝ) < t := ht
    set T0 := (1 + t) / 2 with hT0def
    have hT0 : (1:ℝ) < T0 := by rw [hT0def]; linarith
    have htT0 : T0 < t := by rw [hT0def]; linarith
    have hmem : t ∈ Set.Ici T0 := le_of_lt htT0
    have hsub : Set.Ioi T0 ⊆ Set.Ici T0 := by
      intro x hx
      rw [Set.mem_Ioi] at hx
      rw [Set.mem_Ici]
      exact le_of_lt hx
    have hwithin : ContinuousWithinAt zR (Set.Ioi T0) t :=
      ((hzRIci T0 hT0) t hmem).mono hsub
    apply hwithin.mono_of_mem_nhdsWithin
    first
    | exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htT0)
    | exact nhdsWithin_le_nhds (Ioi_mem_nhds htT0)
  -- patched versions, globally measurable
  set F := Set.piecewise (Set.Ioi (1:ℝ)) (FkOdd k) (fun _ => 0) with hF
  set Z := Set.piecewise (Set.Ioi (1:ℝ)) zR (fun _ => 0) with hZ
  set D := Set.piecewise (Set.Ioi (1:ℝ)) zetaRderiv (fun _ => 0) with hD
  have hFm : Measurable F := patch_measurable _ (FkOdd_continuousOn_Ioi k)
  have hZm : Measurable Z := patch_measurable _ hzRcont
  have hDm : Measurable D := patch_measurable _ zetaRderiv_continuousOn_Ioi
  have hcomp : AEMeasurable (fun u : ℝ => F (sOf u) * (Z (sOf u) / (-D (sOf u))))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    apply AEMeasurable.mul
    · exact hFm.comp_aemeasurable sOf_aemeasurable
    · apply AEMeasurable.div
      · exact hZm.comp_aemeasurable sOf_aemeasurable
      · exact (hDm.comp_aemeasurable sOf_aemeasurable).neg
  apply hcomp.congr
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hu0 : (0:ℝ) < u := hu
  have hs1 : sOf u ∈ Set.Ioi (1:ℝ) := sOf_mem u hu0
  simp only [hF, hZ, hD, Set.piecewise_eq_of_mem _ _ _ hs1, hzR]

/-- MAIN1 and MAIN2 are AEMeasurable everywhere: finite sums of
u^m * exp(-c u), all continuous. -/
theorem oddSplitMain_aemeasurable (bHatOdd : ℕ → ℂ) (k : ℕ) (μ : MeasureTheory.Measure ℝ) :
    AEMeasurable (fun u : ℝ => oddSplitMain1 k u) μ ∧
    AEMeasurable (fun u : ℝ => oddSplitMain2 bHatOdd k u) μ := by
  constructor
  · apply Continuous.aemeasurable
    unfold oddSplitMain1
    apply Continuous.mul _ (Real.continuous_exp.comp continuous_neg)
    apply continuous_finset_sum
    intro j _
    apply Continuous.div_const
    exact Continuous.mul continuous_const (continuous_pow _)
  · apply Continuous.aemeasurable
    unfold oddSplitMain2
    apply Continuous.mul _ (Real.continuous_exp.comp (by continuity))
    apply continuous_finset_sum
    intro j _
    apply Continuous.div_const
    exact Continuous.mul continuous_const (continuous_pow _)

/-- The difference D = integrand - MAIN1 - MAIN2 is integrable on Ioi 0.

On Ioi U it is dominated by leaf 1's majorant, whose integrability leaf 2
establishes; on Ioc 0 U it is bounded on a set of finite measure. -/
theorem oddDiff_integrable (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ) (S : ℝ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hd : OddDomFacts dom betaFam bHatOdd S) (k : ℕ) (hk : 1 ≤ k)
    (hsum : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - zOmegaHom s z (p : ℕ))⁻¹))
    (hcd1 : ∀ s : ℝ, 1 < s →
      ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ∀ s : ℝ, 1 < s → ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u)
      (Set.Ioi (0:ℝ)) := by
  classical
  obtain ⟨CE, hCE, U, hU, hsplit⟩ := oddIntegrand_split dom betaFam bHatOdd S hf hd k
  set D : ℝ → ℝ := fun u => (∑ j ∈ Finset.range (k + 1),
      (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
    * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
    - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u with hDdef
  -- measurability of D on any restriction
  have hDmeas : ∀ (t : Set ℝ), t ⊆ Set.Ioi (0:ℝ) → MeasurableSet t →
      AEMeasurable D (MeasureTheory.volume.restrict t) := by
    intro t hsub ht
    rw [hDdef]
    have hI : AEMeasurable
        (fun u : ℝ => FkOdd k (sOf u)
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
        (MeasureTheory.volume.restrict t) :=
      (oddIntegrand_aemeasurable k).mono_measure
        (MeasureTheory.Measure.restrict_mono hsub le_rfl)
    have hI' : AEMeasurable
        (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
        (MeasureTheory.volume.restrict t) := by
      apply hI.congr
      filter_upwards [MeasureTheory.self_mem_ae_restrict ht] with u hu
      have hu0 : (0:ℝ) < u := hsub hu
      have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
      congr 1
      have hexp := FkOdd_expansion' k hk (sOf u) hs1
        (hsum (sOf u) hs1) (hmul3 (sOf u) hs1) (hcd1 (sOf u) hs1) (hcd2 (sOf u) hs1)
      rw [uOf_sOf u hu0] at hexp
      have hre := congrArg Complex.re hexp
      simp only [Complex.ofReal_re] at hre
      rw [hre, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hcast : (hCoeff (sOf u) j * (u:ℂ) ^ (k - j)
            / ((Nat.factorial (k - j) : ℕ) : ℂ))
          = hCoeff (sOf u) j
            * (((u ^ (k - j) / (Nat.factorial (k - j) : ℝ) : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hm := oddSplitMain_aemeasurable bHatOdd k (MeasureTheory.volume.restrict t)
    exact (hI'.sub hm.1).sub hm.2
  -- the far piece: dominated by leaf 1's majorant
  have hIoiU : Set.Ioi U ⊆ Set.Ioi (0:ℝ) := fun x hx => lt_trans hU hx
  have hIocU : Set.Ioc (0:ℝ) U ⊆ Set.Ioi (0:ℝ) := fun x hx => hx.1
  have hfar : MeasureTheory.IntegrableOn D (Set.Ioi U) := by
    -- dominated by leaf 1's majorant, integrable by leaf 2's Gamma argument
    have hmaj : MeasureTheory.IntegrableOn
        (fun u : ℝ => CE * (∑ j ∈ Finset.range (k + 1),
          dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
        (Set.Ioi U) := by
      have hIoi0 : MeasureTheory.IntegrableOn
          (fun u : ℝ => CE * (∑ j ∈ Finset.range (k + 1),
            dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
          (Set.Ioi (0:ℝ)) := by
        have hrw : (fun u : ℝ => CE * (∑ j ∈ Finset.range (k + 1),
              dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
            = fun u : ℝ => ∑ j ∈ Finset.range (k + 1),
              (CE * dom j / (Nat.factorial (k - j))
                * (u ^ (k - j) * Real.exp (-(3 * u)))) := by
          funext u
          have h3u : (-3 : ℝ) * u = -(3 * u) := by ring
          rw [h3u, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hrw]
        apply MeasureTheory.integrable_finset_sum
        intro j _
        apply MeasureTheory.Integrable.const_mul
        have hgam : MeasureTheory.IntegrableOn
            (fun x : ℝ => Real.exp (-x) * x ^ (((k - j : ℕ) : ℝ) + 1 - 1)) (Set.Ioi 0) :=
          Real.GammaIntegral_convergent (by positivity)
        simp only [add_sub_cancel_right] at hgam
        have hgam' : MeasureTheory.IntegrableOn
            (fun x : ℝ => x ^ ((k - j : ℕ)) * Real.exp (-x)) (Set.Ioi 0) := by
          apply hgam.congr_fun _ measurableSet_Ioi
          intro x _
          simp only
          rw [← Real.rpow_natCast x (k - j)]
          ring
        apply MeasureTheory.Integrable.mono hgam'
        · apply MeasureTheory.AEStronglyMeasurable.mul <;>
            (apply Continuous.aestronglyMeasurable; fun_prop)
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : (0:ℝ) < x := hx
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos (Real.exp_pos (-(3*x))), abs_of_pos (Real.exp_pos (-x))]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp.mpr
          linarith
      exact hIoi0.mono_set hIoiU
    apply MeasureTheory.Integrable.mono' hmaj
      ((hDmeas _ hIoiU measurableSet_Ioi).aestronglyMeasurable)
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with u hu
    have huU : U ≤ u := le_of_lt hu
    rw [Real.norm_eq_abs]
    exact hsplit u huU
  -- the near piece: bounded on a finite-measure set
  have hnear : MeasureTheory.IntegrableOn D (Set.Ioc (0:ℝ) U) := by
    -- D is a difference of three pieces, each integrable on Ioc 0 U
    have hIocmeas : MeasurableSet (Set.Ioc (0:ℝ) U) := measurableSet_Ioc
    -- the integrand transfers from the s-side
    -- -zeta'(s) >= log 2 * 2^-s, from the n = 1 term alone
    have hderivlb : ∀ s : ℝ, 1 < s →
        Real.log 2 * (2:ℝ) ^ (-s) ≤ -zetaRderiv s := by
      intro t ht
      unfold zetaRderiv
      have hsum := log_rpow_summable t ht
      have hneg : (∑' n : ℕ, (-Real.log ((n:ℝ) + 1)) * ((n:ℝ) + 1) ^ (-t))
          = -∑' n : ℕ, Real.log ((n:ℝ) + 1) * ((n:ℝ) + 1) ^ (-t) := by
        rw [← tsum_neg]
        apply tsum_congr
        intro n
        ring
      rw [hneg, neg_neg]
      have hle := hsum.le_tsum 1 (fun n _ => by
        apply mul_nonneg _ (by positivity)
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith)
      have hterm : Real.log 2 * (2:ℝ) ^ (-t)
          = Real.log (((1:ℕ):ℝ) + 1) * (((1:ℕ):ℝ) + 1) ^ (-t) := by
        norm_num
      rw [hterm]
      exact hle
    -- zeta(s) <= zeta(2) for s >= 2, termwise
    have hzetaub : ∀ s : ℝ, 2 ≤ s →
        (∑' n : ℕ, ((n:ℝ) + 1) ^ (-s)) ≤ ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(2:ℝ)) := by
      intro t ht
      have ht1 : (1:ℝ) < t := by linarith
      apply Summable.tsum_le_tsum _ (zetaR_summable t ht1) (zetaR_summable 2 (by norm_num))
      intro n
      have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    -- The integrand equals FkOdd k (sOf u) * J(u) on Ioc 0 U (the hrw identity),
    -- and is bounded there: FkOdd decays like 3^(-k sOf u) while J grows like 2^(sOf u).
    have hIint : MeasureTheory.IntegrableOn
        (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
        (Set.Ioc (0:ℝ) U) := by
      have hSU1 : (1:ℝ) < sOf U := sOf_mem U hU
      set Z32 := ∑' n : ℕ, ((n:ℝ) + 1) ^ (-((3:ℝ)/2)) with hZ32
      set ZU := ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf U)) with hZU
      have hZ32pos : (0:ℝ) < Z32 := by rw [hZ32]; exact zetaR_pos _ (by norm_num)
      have hZUpos : (0:ℝ) < ZU := by rw [hZU]; exact zetaR_pos _ hSU1
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hFkU : (0:ℝ) ≤ FkOdd k (sOf U) := by
        unfold FkOdd
        apply tsum_nonneg
        intro n; positivity
      -- uniform bound: |integrand| <= Z2 * Z2 / (log 2 * 2^-2) on Ioc 0 U
      have hbdd : ∀ u ∈ Set.Ioc (0:ℝ) U,
          ‖(∑ j ∈ Finset.range (k + 1),
              (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
            * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))‖
          ≤ (Z32 + FkOdd k (sOf U)) * ZU * ((2:ℝ) ^ ((3:ℝ)/2) / Real.log 2) := by
        intro u hu
        have hu0 : (0:ℝ) < u := hu.1
        have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
        -- the coefficient sum equals FkOdd k (sOf u), bounded by Z2 termwise
        have hFk : (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
            = FkOdd k (sOf u) := by
          have hexp := FkOdd_expansion' k hk (sOf u) hs1
            (hsum (sOf u) hs1) (hmul3 (sOf u) hs1) (hcd1 (sOf u) hs1) (hcd2 (sOf u) hs1)
          rw [uOf_sOf u hu0] at hexp
          have hre := congrArg Complex.re hexp
          simp only [Complex.ofReal_re] at hre
          rw [hre, Complex.re_sum]
          symm
          apply Finset.sum_congr rfl
          intro j _
          have hcast : (hCoeff (sOf u) j * (u:ℂ) ^ (k - j)
                / ((Nat.factorial (k - j) : ℕ) : ℂ))
              = hCoeff (sOf u) j
                * (((u ^ (k - j) / (Nat.factorial (k - j) : ℝ) : ℝ)) : ℂ) := by
            push_cast
            ring
          rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        rw [hFk, Real.norm_eq_abs, abs_mul]
        -- |FkOdd| = FkOdd (nonneg); |J| <= ZU * 2^s / log2 via hderivlb and antitonicity
        have hsu : sOf U ≤ sOf u := by
          have : u ≤ U := hu.2
          rcases eq_or_lt_of_le this with heq | hlt
          · rw [heq]
          · exact le_of_lt (sOf_strictAntiOn (Set.mem_Ioi.mpr hu0)
              (Set.mem_Ioi.mpr hU) hlt)
        have hFnn : (0:ℝ) ≤ FkOdd k (sOf u) := by
          unfold FkOdd
          apply tsum_nonneg
          intro n; positivity
        have hZle : (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) ≤ ZU := by
          rw [hZU]
          apply Summable.tsum_le_tsum _ (zetaR_summable _ hs1) (zetaR_summable _ hSU1)
          intro n
          have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
            have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
            linarith
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have hJ : |(∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))|
            ≤ ZU * ((2:ℝ) ^ (sOf u) / Real.log 2) := by
          have hden := hderivlb (sOf u) hs1
          have hdpos : (0:ℝ) < Real.log 2 * (2:ℝ) ^ (-(sOf u)) := by
            apply mul_pos hlog2
            exact Real.rpow_pos_of_pos (by norm_num) _
          have hdenpos : (0:ℝ) < -zetaRderiv (sOf u) := lt_of_lt_of_le hdpos hden
          have hnumpos : (0:ℝ) < ∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u)) :=
            zetaR_pos _ hs1
          rw [abs_div, abs_of_pos hnumpos, abs_of_pos hdenpos]
          rw [div_le_iff₀ hdenpos]
          have hpow : (2:ℝ) ^ (sOf u) * (2:ℝ) ^ (-(sOf u)) = 1 := by
            rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
            simp
          calc (∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) ≤ ZU := hZle
            _ = ZU * ((2:ℝ) ^ (sOf u) / Real.log 2) * (Real.log 2 * (2:ℝ) ^ (-(sOf u))) := by
                field_simp
                rw [mul_comm ((2:ℝ) ^ (sOf u)) ((2:ℝ) ^ (-(sOf u))), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
                simp
            _ ≤ ZU * ((2:ℝ) ^ (sOf u) / Real.log 2) * (-zetaRderiv (sOf u)) := by
                apply mul_le_mul_of_nonneg_left hden
                apply mul_nonneg (le_of_lt hZUpos)
                positivity
        have hFbound : FkOdd k (sOf u)
            ≤ (Z32 + FkOdd k (sOf U)) * (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by
          rcases le_or_gt ((3:ℝ)/2) (sOf u) with hreg | hreg
          · -- regime A: s >= 3/2, use FkOdd_le_pow with tau = 3/2
            have hA := FkOdd_le_pow k ((3:ℝ)/2) (sOf u) (by norm_num) hreg
            refine le_trans hA ?_
            rw [← hZ32]
            -- 3^(-k(s-3/2)) * Z32 <= (Z32 + F) * 2^(-s) * 2^(3/2)
            have hkey : (3:ℝ) ^ (-(k:ℝ) * (sOf u - 3/2))
                ≤ (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by
              have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
              have hd0 : (0:ℝ) ≤ sOf u - 3/2 := by linarith [hreg]
              -- 3^(-k d) <= 3^(-d) <= 2^(-d), where d = s - 3/2
              have h1 : (3:ℝ) ^ (-(k:ℝ) * (sOf u - 3/2)) ≤ (3:ℝ) ^ (-(sOf u - 3/2)) := by
                apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                nlinarith [hk1, hd0]
              have h2 : (3:ℝ) ^ (-(sOf u - 3/2)) ≤ (2:ℝ) ^ (-(sOf u - 3/2)) :=
                Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by linarith [hd0])
              have h3 : (2:ℝ) ^ (-(sOf u - 3/2))
                  = (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by
                rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
                congr 1
                ring
              linarith [h1, h2, h3.le, h3.ge]
            calc (3:ℝ) ^ (-(k:ℝ) * (sOf u - 3/2)) * Z32
                ≤ ((2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2)) * Z32 :=
                  mul_le_mul_of_nonneg_right hkey (le_of_lt hZ32pos)
              _ ≤ (Z32 + FkOdd k (sOf U)) * (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by
                  have hp1 : (0:ℝ) < (2:ℝ) ^ (-(sOf u)) :=
                    Real.rpow_pos_of_pos (by norm_num) _
                  have hp2 : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/2) :=
                    Real.rpow_pos_of_pos (by norm_num) _
                  have hle : Z32 ≤ Z32 + FkOdd k (sOf U) := by linarith
                  calc ((2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2)) * Z32
                      = Z32 * (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by ring
                    _ ≤ (Z32 + FkOdd k (sOf U)) * (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by
                        apply mul_le_mul_of_nonneg_right _ (le_of_lt hp2)
                        exact mul_le_mul_of_nonneg_right hle (le_of_lt hp1)
          · -- regime B: s < 3/2, s is bounded so use antitonicity
            have hB := FkOdd_antitone k (sOf U) (sOf u) hSU1 hsu
            refine le_trans hB ?_
            have h2s : (1:ℝ) ≤ (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2) := by
              rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
              have hexp : (0:ℝ) ≤ -(sOf u) + (3:ℝ)/2 := by linarith [hreg]
              have h20 : (2:ℝ) ^ (0:ℝ) = 1 := by simp
              rw [← h20]
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
            nlinarith [hFkU, hZ32pos, h2s]
        -- combine: |F| * |J| <= (Z32+F_U) 2^-s 2^(3/2) * ZU 2^s / log2
        --                     = (Z32+F_U) ZU 2^(3/2) / log2   since 2^-s 2^s = 1
        have hJnn : (0:ℝ) ≤ |(∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))| :=
          abs_nonneg _
        have hFabs : |FkOdd k (sOf u)| = FkOdd k (sOf u) := abs_of_nonneg hFnn
        rw [hFabs]
        have hBnn : (0:ℝ) ≤ (Z32 + FkOdd k (sOf U)) * (2:ℝ) ^ (-(sOf u))
            * (2:ℝ) ^ ((3:ℝ)/2) := by
          apply mul_nonneg (mul_nonneg (by linarith [hZ32pos, hFkU]) _)
          · exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
          · exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
        have hstep := mul_le_mul hFbound hJ hJnn hBnn
        refine le_trans hstep ?_
        have hcancel : (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ (sOf u) = 1 := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          simp
        calc (Z32 + FkOdd k (sOf U)) * (2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ ((3:ℝ)/2)
              * (ZU * ((2:ℝ) ^ (sOf u) / Real.log 2))
            = (Z32 + FkOdd k (sOf U)) * ZU * ((2:ℝ) ^ ((3:ℝ)/2) / Real.log 2)
              * ((2:ℝ) ^ (-(sOf u)) * (2:ℝ) ^ (sOf u)) := by ring
          _ = (Z32 + FkOdd k (sOf U)) * ZU * ((2:ℝ) ^ ((3:ℝ)/2) / Real.log 2) := by
              rw [hcancel, mul_one]
          _ ≤ (Z32 + FkOdd k (sOf U)) * ZU * ((2:ℝ) ^ ((3:ℝ)/2) / Real.log 2) :=
              le_refl _
      have hmeas : AEMeasurable
          (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
              (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
            * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
          (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) U)) := by
        have hI : AEMeasurable
            (fun u : ℝ => FkOdd k (sOf u)
              * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
            (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) U)) :=
          (oddIntegrand_aemeasurable k).mono_measure
            (MeasureTheory.Measure.restrict_mono hIocU le_rfl)
        apply hI.congr
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
        have hu0 : (0:ℝ) < u := hu.1
        have hs1 : (1:ℝ) < sOf u := sOf_mem u hu0
        congr 1
        have hexp := FkOdd_expansion' k hk (sOf u) hs1
          (hsum (sOf u) hs1) (hmul3 (sOf u) hs1) (hcd1 (sOf u) hs1) (hcd2 (sOf u) hs1)
        rw [uOf_sOf u hu0] at hexp
        have hre := congrArg Complex.re hexp
        simp only [Complex.ofReal_re] at hre
        rw [hre, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hcast : (hCoeff (sOf u) j * (u:ℂ) ^ (k - j)
              / ((Nat.factorial (k - j) : ℕ) : ℂ))
            = hCoeff (sOf u) j
              * (((u ^ (k - j) / (Nat.factorial (k - j) : ℝ) : ℝ)) : ℂ) := by
          push_cast
          ring
        rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      exact ⟨hmeas.aestronglyMeasurable,
        MeasureTheory.HasFiniteIntegral.restrict_of_bounded
          (C := (Z32 + FkOdd k (sOf U)) * ZU * ((2:ℝ) ^ ((3:ℝ)/2) / Real.log 2))
          (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
          (by
            filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
            exact hbdd u hu)⟩
    -- MAIN1 and MAIN2 are continuous, hence integrable on a compact-closure set
    have hc1 : Continuous (fun u : ℝ => oddSplitMain1 k u) := by
      unfold oddSplitMain1
      apply Continuous.mul _ (Real.continuous_exp.comp continuous_neg)
      apply continuous_finset_sum
      intro j _
      apply Continuous.div_const
      exact Continuous.mul continuous_const (continuous_pow _)
    have hc2 : Continuous (fun u : ℝ => oddSplitMain2 bHatOdd k u) := by
      unfold oddSplitMain2
      apply Continuous.mul _ (Real.continuous_exp.comp (by continuity))
      apply continuous_finset_sum
      intro j _
      apply Continuous.div_const
      exact Continuous.mul continuous_const (continuous_pow _)
    have hM1 : MeasureTheory.IntegrableOn (fun u : ℝ => oddSplitMain1 k u)
        (Set.Ioc (0:ℝ) U) := hc1.integrableOn_Ioc
    have hM2 : MeasureTheory.IntegrableOn (fun u : ℝ => oddSplitMain2 bHatOdd k u)
        (Set.Ioc (0:ℝ) U) := hc2.integrableOn_Ioc
    rw [hDdef]
    exact (hIint.sub hM1).sub hM2
  have hunion : Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) U ∪ Set.Ioi U := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      rcases lt_or_ge U x with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · linarith
  rw [hunion]
  exact hnear.union hfar

/-- (j+3)^3 (2/3)^j is bounded by its value at j = 4, from polyGeom_step. -/
theorem polyGeom_bounded (j : ℕ) :
    ((j:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ j ≤ (7:ℝ) ^ 3 * ((2:ℝ)/3) ^ 4 := by
  rcases Nat.lt_or_ge j 4 with hlt | hge
  · interval_cases j <;> norm_num
  · induction j, hge using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        have hstep := polyGeom_step n hn
        push_cast at hstep ⊢
        linarith [hstep, ih]

/-- (j+3)^3 (8/9)^j is bounded, by the same ratio argument as polyGeom_step
but at 8/9: the ratio is ((j+4)/(j+3))^3 (8/9) < 1 once j+3 > 25.4, and the
max sits at j = 22. -/
theorem polyGeom_step89 (j : ℕ) (hj : 22 ≤ j) :
    ((j:ℝ) + 4) ^ 3 * ((8:ℝ)/9) ^ (j+1) ≤ ((j:ℝ) + 3) ^ 3 * ((8:ℝ)/9) ^ j := by
  have hj22 : (22:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hpos : (0:ℝ) < ((8:ℝ)/9) ^ j := pow_pos (by norm_num) j
  have hcube : ((j:ℝ) + 4) ^ 3 * (8/9) ≤ ((j:ℝ) + 3) ^ 3 := by
    nlinarith [hj22, sq_nonneg ((j:ℝ) + 3), sq_nonneg ((j:ℝ) - 22)]
  have he : ((8:ℝ)/9) ^ (j+1) = ((8:ℝ)/9) ^ j * (8/9) := pow_succ _ _
  rw [he]
  calc ((j:ℝ)+4)^3 * (((8:ℝ)/9)^j * (8/9))
      = (((j:ℝ)+4)^3 * (8/9)) * ((8:ℝ)/9)^j := by ring
    _ ≤ ((j:ℝ)+3)^3 * ((8:ℝ)/9)^j :=
        mul_le_mul_of_nonneg_right hcube (le_of_lt hpos)

theorem polyGeom_bounded89 (j : ℕ) :
    ((j:ℝ) + 3) ^ 3 * ((8:ℝ)/9) ^ j ≤ (26:ℝ) ^ 3 * ((8:ℝ)/9) ^ 22 := by
  rcases Nat.lt_or_ge j 22 with hlt | hge
  · interval_cases j <;> norm_num
  · induction j, hge using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        have hstep := polyGeom_step89 n hn
        push_cast at hstep ⊢
        linarith [hstep, ih]

/-- Cubic growth is dominated by 2^d: (m+d)^3 <= m^3 2^d for m >= 4. -/
theorem cube_le_two_pow (m d : ℕ) (hm : 4 ≤ m) :
    (((m + d : ℕ)):ℝ) ^ 3 ≤ ((m:ℝ)) ^ 3 * 2 ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
      have hm4 : (4:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hstep : (((m + (n+1) : ℕ)):ℝ) ^ 3 ≤ 2 * (((m + n : ℕ)):ℝ) ^ 3 := by
        push_cast
        nlinarith [hm4, hn, sq_nonneg ((m:ℝ) + n), sq_nonneg ((m:ℝ) + n - 4)]
      calc (((m + (n+1) : ℕ)):ℝ) ^ 3 ≤ 2 * (((m + n : ℕ)):ℝ) ^ 3 := hstep
        _ ≤ 2 * (((m:ℝ)) ^ 3 * 2 ^ n) := by linarith [ih]
        _ = ((m:ℝ)) ^ 3 * 2 ^ (n+1) := by ring

/-- The polynomial-weighted tail: summing dom_decay's bound over j > k keeps
the (k+3)^3 3^-k shape rather than degrading to a worse geometric ratio. -/
theorem poly_tail_bound (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun d : ℕ => (((k + 4 + d : ℕ)):ℝ) ^ 3
        * (3:ℝ) ^ (-((k + 1 + d : ℕ)):ℝ)) ∧
    ∑' d : ℕ, (((k + 4 + d : ℕ)):ℝ) ^ 3 * (3:ℝ) ^ (-((k + 1 + d : ℕ)):ℝ)
      ≤ 2 * ((k:ℝ) + 3) ^ 3 * (3:ℝ) ^ (-(k:ℝ)) := by
  have hk4 : 4 ≤ k + 4 := by omega
  -- termwise: (k+4+d)^3 3^-(k+1+d) <= (k+4)^3 3^-(k+1) (2/3)^d
  have hterm : ∀ d : ℕ,
      (((k + 4 + d : ℕ)):ℝ) ^ 3 * (3:ℝ) ^ (-((k + 1 + d : ℕ)):ℝ)
        ≤ (((k + 4 : ℕ)):ℝ) ^ 3 * (3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) * ((2:ℝ)/3) ^ d := by
    intro d
    have hc := cube_le_two_pow (k + 4) d hk4
    have h3 : (3:ℝ) ^ (-((k + 1 + d : ℕ)):ℝ)
        = (3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) * (3:ℝ) ^ (-(d:ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      congr 1
      push_cast
      ring
    rw [h3]
    have h3d : (3:ℝ) ^ (-(d:ℝ)) = ((1:ℝ)/3) ^ d := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
      rw [div_pow, one_pow]
      exact inv_eq_one_div _
    rw [h3d]
    have hpos : (0:ℝ) < (3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hcalc : (((k + 4 + d : ℕ)):ℝ) ^ 3 * ((3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) * ((1:ℝ)/3) ^ d)
        ≤ ((((k + 4 : ℕ)):ℝ) ^ 3 * 2 ^ d) * ((3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) * ((1:ℝ)/3) ^ d) := by
      apply mul_le_mul_of_nonneg_right hc
      positivity
    refine le_trans hcalc ?_
    have hsplit : ((2:ℝ)/3) ^ d = (2:ℝ) ^ d * ((1:ℝ)/3) ^ d := by
      rw [← mul_pow]; norm_num
    rw [hsplit]
    ring_nf
    exact le_refl _
  -- sum the geometric majorant
  have hgeo : Summable (fun d : ℕ =>
      (((k + 4 : ℕ)):ℝ) ^ 3 * (3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) * ((2:ℝ)/3) ^ d) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hlhs : Summable (fun d : ℕ =>
      (((k + 4 + d : ℕ)):ℝ) ^ 3 * (3:ℝ) ^ (-((k + 1 + d : ℕ)):ℝ)) := by
    apply Summable.of_nonneg_of_le _ hterm hgeo
    intro d
    positivity
  refine ⟨hlhs, ?_⟩
  refine le_trans (Summable.tsum_le_tsum hterm hlhs hgeo) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have hone : (1:ℝ) - 2/3 = 1/3 := by norm_num
  rw [hone]
  have h3 : (3:ℝ) ^ (-((k + 1 : ℕ)):ℝ) = (3:ℝ) ^ (-(k:ℝ)) * (1/3) := by
    rw [show (-((k + 1 : ℕ)):ℝ) = -(k:ℝ) + (-(1:ℝ)) from by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    norm_num
  rw [h3]
  have hkk : (((k + 4 : ℕ)):ℝ) ^ 3 ≤ 2 * ((k:ℝ) + 3) ^ 3 := by
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    push_cast
    nlinarith [hk1, sq_nonneg ((k:ℝ) + 3)]
  have hp : (0:ℝ) < (3:ℝ) ^ (-(k:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hkk, hp]

/-- The absorption at ratio 3/4, for the b_j 2^j tail: dom decays like 3^-j,
so dom_j 2^j decays like (2/3)^j up to the binomial factor, which (3/4)^j
absorbs. -/
theorem binom_absorb_two (S : ℝ) (hS : 0 ≤ S) :
    ∃ C'' > 0, ∀ j : ℕ,
      (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) * (2:ℝ) ^ j
        ≤ C'' * ((3:ℝ)/4) ^ j := by
  refine ⟨(26:ℝ) ^ 3 * ((8:ℝ)/9) ^ 22 * S / 6 + 1, by positivity, ?_⟩
  intro j
  have hbin : (Nat.choose (j + 3) 3 : ℝ) ≤ ((j:ℝ) + 3) ^ 3 / 6 := by
    rw [choose_three_real]
    have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    nlinarith [hj]
  have hsplit : (3:ℝ) ^ (-(j:ℝ)) * (2:ℝ) ^ j = ((8:ℝ)/9) ^ j * ((3:ℝ)/4) ^ j := by
    rw [← mul_pow]
    have h89 : ((8:ℝ)/9) * ((3:ℝ)/4) = (2:ℝ)/3 := by norm_num
    rw [h89]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
    rw [div_pow]
    rw [inv_mul_eq_div]
  have hmul : (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) * (2:ℝ) ^ j
      = (Nat.choose (j + 3) 3 : ℝ) * S * ((3:ℝ) ^ (-(j:ℝ)) * (2:ℝ) ^ j) := by ring
  rw [hmul, hsplit]
  have hpg := polyGeom_bounded89 j
  have h34 : (0:ℝ) < ((3:ℝ)/4) ^ j := by positivity
  calc (Nat.choose (j + 3) 3 : ℝ) * S * (((8:ℝ)/9) ^ j * ((3:ℝ)/4) ^ j)
      ≤ (((j:ℝ) + 3) ^ 3 / 6) * S * (((8:ℝ)/9) ^ j * ((3:ℝ)/4) ^ j) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hbin hS
    _ = (((j:ℝ) + 3) ^ 3 * ((8:ℝ)/9) ^ j) * S / 6 * ((3:ℝ)/4) ^ j := by ring
    _ ≤ ((26:ℝ) ^ 3 * ((8:ℝ)/9) ^ 22) * S / 6 * ((3:ℝ)/4) ^ j := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h34)
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hpg hS
    _ ≤ ((26:ℝ) ^ 3 * ((8:ℝ)/9) ^ 22 * S / 6 + 1) * ((3:ℝ)/4) ^ j := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h34)
        linarith

theorem binom_absorb (S : ℝ) (hS : 0 ≤ S) :
    ∃ C' > 0, ∀ j : ℕ,
      (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) ≤ C' * ((1:ℝ)/2) ^ j := by
  refine ⟨(7:ℝ) ^ 3 * ((2:ℝ)/3) ^ 4 * S / 6 + 1, by positivity, ?_⟩
  intro j
  have hbin : (Nat.choose (j + 3) 3 : ℝ) ≤ ((j:ℝ) + 3) ^ 3 / 6 := by
    rw [choose_three_real]
    have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    nlinarith [hj]
  have hsplit : (3:ℝ) ^ (-(j:ℝ)) = ((2:ℝ)/3) ^ j * ((1:ℝ)/2) ^ j := by
    rw [← mul_pow]
    have h13 : ((2:ℝ)/3) * ((1:ℝ)/2) = (1:ℝ)/3 := by norm_num
    rw [h13, div_pow, one_pow]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
    exact inv_eq_one_div _
  rw [hsplit]
  have hpg := polyGeom_bounded j
  have hhalf : (0:ℝ) < ((1:ℝ)/2) ^ j := by positivity
  have h23 : (0:ℝ) < ((2:ℝ)/3) ^ j := by positivity
  calc (Nat.choose (j + 3) 3 : ℝ) * S * (((2:ℝ)/3) ^ j * ((1:ℝ)/2) ^ j)
      ≤ (((j:ℝ) + 3) ^ 3 / 6) * S * (((2:ℝ)/3) ^ j * ((1:ℝ)/2) ^ j) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hbin hS
    _ = (((j:ℝ) + 3) ^ 3 * ((2:ℝ)/3) ^ j) * S / 6 * ((1:ℝ)/2) ^ j := by ring
    _ ≤ ((7:ℝ) ^ 3 * ((2:ℝ)/3) ^ 4) * S / 6 * ((1:ℝ)/2) ^ j := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hhalf)
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hpg hS
    _ ≤ ((7:ℝ) ^ 3 * ((2:ℝ)/3) ^ 4 * S / 6 + 1) * ((1:ℝ)/2) ^ j := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hhalf)
        linarith

/-- The far-piece hypothesis of `fOdd_expansion_final` is satisfiable: suitable
CE and U exist, by LEAF 1.  They are parameters of the main theorem rather than
existentials because `hMR`, `hCN` and `hNEARU` must mention them. -/
theorem fOdd_expansion_hsplitD_exists (dom betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (S : ℝ) (hf : OddCoeffFacts betaFam bHatOdd)
    (hd : OddDomFacts dom betaFam bHatOdd S) (k : ℕ) :
    ∃ CE > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      |(∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u|
      ≤ CE * (∑ j ∈ Finset.range (k + 1),
          dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u) :=
  oddIntegrand_split dom betaFam bHatOdd S hf hd k

set_option maxHeartbeats 4000000 in
/-- STEP 5, the target: this is exactly OddNumericalFacts.remainder.

    fOdd k = 1/2 + beta 2^-k + R_k,   |R_k| <= MR (2/9)^k

Route: fOdd_u_form, then the integrand splits as
oddSplitMain1 + oddSplitMain2 + rest, with the two main integrals above and
`rest` bounded via gamma_normalised_three (each error factor is O(e^-3u)
against a polynomial in u). -/
theorem fOdd_expansion_final (MR CE U : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hCEpos : 0 < CE) (hUpos : 0 < U)
    (hsum1 : Summable (fun n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n)))
    (hsum : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - zOmegaHom s z (p : ℕ))⁻¹))
    (hcd1 : ∀ s : ℝ, 1 < s →
      ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ∀ s : ℝ, 1 < s → ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0)
    (betaFam : ℕ → ℝ) (bHatOdd : ℕ → ℂ)
    (hf : OddCoeffFacts betaFam bHatOdd)
    (hdiff : ∀ t : ℝ, 1 ≤ t →
      DifferentiableOn ℂ (fun w => Hodd t w) (Metric.ball 0 4))
    -- The certified dominating sequence and coefficient sum of PROOF.md (5.5).
    -- dom bounds |h_j(1)|, |b_j| and betaFam j simultaneously; S = sum_i |g_i| 3^i
    -- over the coefficients of G_2 = d_s^2 H (1 - z/3)^3, certified S <= 14414
    -- (head i <= 16 by interval recursion, tail by Cauchy).
    (dom : ℕ → ℝ) (S : ℝ) (hS0 : 0 ≤ S)
    (hd : OddDomFacts dom betaFam bHatOdd S)
    (S0 S1 : ℝ) (ht : OddTailFacts bHatOdd S0 S1)
    -- The near-piece constant.  FkOdd k s <= CN 3^-k holds for each fixed
    -- s > 1 (the index set has every n >= 3^k), with CN depending on s = sOf U;
    -- it blows up only as s -> 1, i.e. as U -> infinity.  CN, NEARU and
    -- hsplitD must all be instantiated at the SAME U; the certified values
    -- CN <= 364 and NEARU <= 24.68 are at U = 3 (cn_recursion.py,
    -- nearu_bound.py), which is also where CE <= 5.48910 is certified.
    (CN : ℝ) (hCNnn : 0 ≤ CN)
    (hCN : FkOdd k (sOf U) ≤ CN * ((1:ℝ)/3) ^ k)
    -- the far-piece bound of LEAF 1, with its constant named.  This is
    -- oddIntegrand_split's conclusion; see fOdd_expansion_hsplitD_exists,
    -- which discharges it.  It is a parameter only because hMR, hCN and
    -- hNEARU must name CE and U.
    (hsplitD : ∀ u : ℝ, U ≤ u →
      |(∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u|
      ≤ CE * (∑ j ∈ Finset.range (k + 1),
          dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
    -- the near-piece weighted sum, certified alongside U
    (NEARU : ℝ)
    (hNEARU : U * (2 + 2 * Real.eulerMascheroniConstant)
        * (∑ j ∈ Finset.range (k + 1),
            dom j * U ^ (k - j) / (Nat.factorial (k - j)))
      ≤ NEARU * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k)
    -- the honest coefficient sum: far piece CE S/18 (three error terms, not the
    -- one of PROOF.md 5.3), both tails, the near piece, and the U-weighted part.
    (hMR : CE * S / 18 + S0 / 2
        + 5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64
        + CN + NEARU ≤ MR) :
    |fOdd k - 1 / 2 - betaOdd * ((1:ℝ)/2) ^ k|
      ≤ MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
  rw [fOdd_u_form k hk hsum1 hsum hmul3 hcd1 hcd2]
  obtain ⟨hM1int, hM2int⟩ := oddSplitMain_integrable bHatOdd k
  have hDint := oddDiff_integrable dom betaFam bHatOdd S hf hd k hk hsum hmul3 hcd1 hcd2
  -- STEP 1: the integral of the difference is the target quantity, up to the
  -- two main integrals and their tails.
  have hsplit_int :
      (∫ u in Set.Ioi (0:ℝ),
        ((∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u))
      = (∫ u in Set.Ioi (0:ℝ),
          (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
        - (∫ u in Set.Ioi (0:ℝ), oddSplitMain1 k u)
        - (∫ u in Set.Ioi (0:ℝ), oddSplitMain2 bHatOdd k u) := by
    have hAint : MeasureTheory.IntegrableOn
        (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
        (Set.Ioi (0:ℝ)) := by
      have h2 := (hDint.add hM1int).add hM2int
      apply h2.congr_fun _ measurableSet_Ioi
      intro u _
      show (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u
          + (fun u : ℝ => oddSplitMain1 k u) u
          + (fun u : ℝ => oddSplitMain2 bHatOdd k u) u
        = _
      ring
    have e1 := MeasureTheory.integral_sub (hAint.sub hM1int) hM2int
    have e2 := MeasureTheory.integral_sub hAint hM1int
    simp only [Pi.sub_apply] at e1
    rw [e2] at e1
    exact e1
  -- STEP 2a: MAIN1's integral is the partial sum, and the full sum is 1/2.
  have hM1val := oddSplitMain1_integral k hk
  have hd1 : DifferentiableOn ℂ (fun w => Hodd 1 w) (Metric.ball 0 4) := hdiff 1 le_rfl
  have hsum1c : HasSum (fun j : ℕ => hCoeff 1 j) (1/2 : ℂ) := hCoeff_sum_one hd1
  have hsummable1 : Summable (fun j : ℕ => hCoeff 1 j) := hsum1c.summable
  have hre1 : HasSum (fun j : ℕ => (hCoeff 1 j).re) (1/2 : ℝ) := by
    have := hsum1c.mapL Complex.reCLM
    simpa using this
  -- the partial sum differs from 1/2 by the tail
  have hsummre1 : Summable (fun j : ℕ => (hCoeff 1 j).re) := hre1.summable
  have hpart1 : ∑ j ∈ Finset.range (k + 1), (hCoeff 1 j).re
      = (1/2 : ℝ) - ∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0) := by
    have hlow : Summable (fun j : ℕ => (if j ≤ k then (hCoeff 1 j).re else 0)) := by
      apply summable_of_finite_support
      apply Set.Finite.subset (Set.finite_Icc 0 k)
      intro j hj
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hj
      obtain ⟨hjk, _⟩ := hj
      exact ⟨Nat.zero_le j, hjk⟩
    have hhigh : Summable (fun j : ℕ => (if k < j then (hCoeff 1 j).re else 0)) := by
      apply Summable.of_norm_bounded (g := fun j : ℕ => |(hCoeff 1 j).re|)
        hsummre1.abs
      intro j
      by_cases hc : k < j
      · simp [hc, Real.norm_eq_abs]
      · simp [hc]
    have hsplit : ∀ j : ℕ, (hCoeff 1 j).re
        = (if j ≤ k then (hCoeff 1 j).re else 0)
          + (if k < j then (hCoeff 1 j).re else 0) := by
      intro j
      by_cases hc : j ≤ k
      · simp [hc, Nat.not_lt.mpr hc]
      · simp [hc, Nat.lt_of_not_le hc]
    have htotal : (1/2 : ℝ)
        = (∑' j : ℕ, (if j ≤ k then (hCoeff 1 j).re else 0))
          + ∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0) := by
      rw [← Summable.tsum_add hlow hhigh]
      rw [← hre1.tsum_eq]
      exact tsum_congr hsplit
    have hfin : (∑' j : ℕ, (if j ≤ k then (hCoeff 1 j).re else 0))
        = ∑ j ∈ Finset.range (k + 1), (hCoeff 1 j).re := by
      rw [tsum_eq_sum (s := Finset.range (k + 1))]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        simp [Nat.lt_succ_iff.mp hj]
      · intro j hj
        rw [Finset.mem_range] at hj
        have hjk : ¬ (j ≤ k) := by omega
        simp [hjk]
    rw [hfin] at htotal
    linarith [htotal]
  -- STEP 2b: MAIN2's integral is 2^-(k+1) times a partial sum, whose full
  -- series is 2*beta by order_two_coefficient.
  have hM2val := oddSplitMain2_integral bHatOdd k hk
  have hord := order_two_coefficient betaFam bHatOdd hf hdiff hd1
  -- STEP 2b: MAIN2's full series is 2*beta.
  have hbnorm : ∀ j : ℕ, ‖bHatOdd j‖ ≤ betaFam j := by
    intro j
    apply le_of_tendsto (hf.tendsto_deriv j).norm
    have hIoo : Set.Ioo (1:ℝ) 2 ∈ nhdsWithin (1:ℝ) (Set.Ioi (1:ℝ)) := by
      have h2 : Set.Iio (2:ℝ) ∈ nhds (1:ℝ) := Iio_mem_nhds (by norm_num)
      have := Filter.inter_mem_inf h2 (Filter.mem_principal_self (Set.Ioi (1:ℝ)))
      rw [nhdsWithin]
      convert this using 1
      ext x
      simp [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
      tauto
    filter_upwards [hIoo] with t ht
    exact hf.deriv_bound j t ht
  have hsum2h : Summable (fun j : ℕ => hCoeff 1 j * 2 ^ j) :=
    (hCoeff_sum_two hd1).summable
  have hsum2c : Summable (fun j : ℕ => bHatOdd j * 2 ^ j) := by
    apply Summable.of_norm_bounded (g := fun j : ℕ => betaFam j * (2:ℝ) ^ j)
      hf.fam_summable
    intro j
    rw [norm_mul, norm_pow]
    have h2n : ‖(2:ℂ)‖ = (2:ℝ) := by simp
    rw [h2n]
    exact mul_le_mul_of_nonneg_right (hbnorm j) (by positivity)
  have hre2 : (∑' j : ℕ, (bHatOdd j).re * 2 ^ j)
      + 2 * Real.eulerMascheroniConstant * (∑' j : ℕ, (hCoeff 1 j).re * 2 ^ j)
      = 2 * betaOdd := by
    have hb : (∑' j : ℕ, bHatOdd j * 2 ^ j).re = ∑' j : ℕ, (bHatOdd j).re * 2 ^ j := by
      rw [Complex.re_tsum hsum2c]
      apply tsum_congr
      intro j
      have h2 : ((2:ℂ) ^ j) = (((2:ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
      rw [h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hh : (∑' j : ℕ, hCoeff 1 j * 2 ^ j).re = ∑' j : ℕ, (hCoeff 1 j).re * 2 ^ j := by
      rw [Complex.re_tsum hsum2h]
      apply tsum_congr
      intro j
      have h2 : ((2:ℂ) ^ j) = (((2:ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
      rw [h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have := congrArg Complex.re hord
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat] at this
    rw [hb, hh] at this
    have him : (∑' j : ℕ, hCoeff 1 j * 2 ^ j).im * (2 * (Real.eulerMascheroniConstant:ℂ)).im = 0 := by
      simp
    simp only [Complex.ofReal_im, mul_zero, sub_zero, zero_mul, mul_zero] at this
    linarith [this]
  have hbr : Summable (fun j : ℕ => (bHatOdd j).re * 2 ^ j) := by
    apply Summable.congr
      (hsum2c.map (Complex.reCLM : ℂ →L[ℝ] ℝ) Complex.reCLM.continuous)
    intro j
    show ((bHatOdd j * 2 ^ j).re : ℝ) = (bHatOdd j).re * 2 ^ j
    have h2 : ((2:ℂ) ^ j) = (((2:ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hhr : Summable (fun j : ℕ => (hCoeff 1 j).re * 2 ^ j) := by
    apply Summable.congr
      (hsum2h.map (Complex.reCLM : ℂ →L[ℝ] ℝ) Complex.reCLM.continuous)
    intro j
    show ((hCoeff 1 j * 2 ^ j).re : ℝ) = (hCoeff 1 j).re * 2 ^ j
    have h2 : ((2:ℂ) ^ j) = (((2:ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcomb : HasSum (fun j : ℕ => ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j)
      ((∑' j : ℕ, (bHatOdd j).re * 2 ^ j)
        + 2 * Real.eulerMascheroniConstant * ∑' j : ℕ, (hCoeff 1 j).re * 2 ^ j) :=
    (hbr.hasSum.add ((hhr.hasSum).mul_left
      (2 * Real.eulerMascheroniConstant))).congr_fun (fun j => by ring)
  have hre2s : HasSum (fun j : ℕ => ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j) (2 * betaOdd) := by
    rw [← hre2]
    exact hcomb

  -- bridge: the indicator tail equals the shifted tail
  -- SUPERSEDED (kept because it is interleaved with live code): everything
  -- from here to STEP 4 computes the two tails through binom_absorb /
  -- geom_tail_bound_cx.  That route bounds |h_j(1)| and |b_j| by dom_j, which
  -- carries the third-order S = 14414 and is far too lossy -- it gives a tail
  -- coefficient of ~67000 against a budget of 4900.  The collection now takes
  -- the tails from ht.tail_h and ht.tail_b instead (S_0 <= 44.6, S_1 <= 486.2,
  -- first- and second-order poles), so none of this is used.
  have hbridge1 : (∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0))
      = ∑' d : ℕ, (hCoeff 1 (d + (k+1))).re := by
    have hstan := hsummre1.sum_add_tsum_nat_add (k+1)
    have htot := hre1.tsum_eq
    rw [htot] at hstan
    rw [hpart1] at hstan
    linarith [hstan]

  -- the shifted tail, bounded by the polynomial tail lemma
  have htail1new : |∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0)|
      ≤ (S / 3) * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    rw [hbridge1]
    have hterm : ∀ d : ℕ, |(hCoeff 1 (d + (k+1))).re|
        ≤ (S / 6) * ((((d + (k+1) : ℕ)):ℝ) + 3) ^ 3 * (3:ℝ) ^ (-(((d + (k+1) : ℕ)):ℝ)) := by
      intro d
      set j := d + (k+1) with hj
      have h1 : |(hCoeff 1 j).re| ≤ dom j := by
        refine le_trans ?_ (hd.dom_h j)
        first
        | exact Complex.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
      have h2 := dom_decay dom betaFam bHatOdd S hd j
      have h3pos : (0:ℝ) < (3:ℝ) ^ j := by positivity
      have h3 : dom j ≤ (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
        rw [le_mul_inv_iff₀ h3pos]
        linarith [h2]
      have h4 : (Nat.choose (j + 3) 3 : ℝ) ≤ ((j:ℝ) + 3) ^ 3 / 6 := by
        rw [choose_three_real]
        have hjn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        nlinarith [hjn]
      have hrp : (0:ℝ) < (3:ℝ) ^ (-(j:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      calc |(hCoeff 1 j).re| ≤ dom j := h1
        _ ≤ (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) := h3
        _ ≤ (((j:ℝ) + 3) ^ 3 / 6) * S * (3:ℝ) ^ (-(j:ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hrp)
            exact mul_le_mul_of_nonneg_right h4 hS0
        _ = (S / 6) * ((j:ℝ) + 3) ^ 3 * (3:ℝ) ^ (-(j:ℝ)) := by ring
    -- sum the termwise bound against poly_tail_bound
    have hsumTail : Summable (fun d : ℕ => (hCoeff 1 (d + (k+1))).re) :=
      (summable_nat_add_iff (k+1)).2 hsummre1
    have hpoly := (poly_tail_bound k hk).1
    have hmajS : Summable (fun d : ℕ =>
        (S / 6) * ((((d + (k+1) : ℕ)):ℝ) + 3) ^ 3
          * (3:ℝ) ^ (-(((d + (k+1) : ℕ)):ℝ))) := by
      apply Summable.congr (hpoly.mul_left (S / 6))
      intro d
      have hidx : ((((d + (k+1) : ℕ)):ℝ) + 3) = (((k + 4 + d : ℕ)):ℝ) := by
        push_cast; ring
      have hidx2 : (-(((d + (k+1) : ℕ)):ℝ)) = (-((k + 1 + d : ℕ)):ℝ) := by
        push_cast; ring
      rw [hidx, hidx2]
      ring
    have habs : |∑' d : ℕ, (hCoeff 1 (d + (k+1))).re|
        ≤ ∑' d : ℕ, (S / 6) * ((((d + (k+1) : ℕ)):ℝ) + 3) ^ 3
            * (3:ℝ) ^ (-(((d + (k+1) : ℕ)):ℝ)) := by
      have hnt : |∑' d : ℕ, (hCoeff 1 (d + (k+1))).re|
          ≤ ∑' d : ℕ, |(hCoeff 1 (d + (k+1))).re| := by
        have := norm_tsum_le_tsum_norm (f := fun d : ℕ => (hCoeff 1 (d + (k+1))).re)
          (by simpa [Real.norm_eq_abs] using hsumTail.abs)
        simpa [Real.norm_eq_abs] using this
      refine le_trans hnt ?_
      exact Summable.tsum_le_tsum hterm hsumTail.abs hmajS
    refine le_trans habs ?_
    have hpt := (poly_tail_bound k hk).2
    have hidx : (∑' d : ℕ, (S / 6) * ((((d + (k+1) : ℕ)):ℝ) + 3) ^ 3
          * (3:ℝ) ^ (-(((d + (k+1) : ℕ)):ℝ)))
        = (S / 6) * ∑' d : ℕ, (((k + 4 + d : ℕ)):ℝ) ^ 3
            * (3:ℝ) ^ (-((k + 1 + d : ℕ)):ℝ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      have h1 : ((((d + (k+1) : ℕ)):ℝ) + 3) = (((k + 4 + d : ℕ)):ℝ) := by
        push_cast; ring
      have h2 : (-(((d + (k+1) : ℕ)):ℝ)) = (-((k + 1 + d : ℕ)):ℝ) := by
        push_cast; ring
      rw [h1, h2]
      ring
    rw [hidx]
    have h3k : (3:ℝ) ^ (-(k:ℝ)) = ((1:ℝ)/3) ^ k := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast,
        div_pow, one_pow]
      exact inv_eq_one_div _
    rw [h3k] at hpt
    have hS6 : (0:ℝ) ≤ S / 6 := by linarith [hS0]
    nlinarith [hpt, hS6]

  -- STEP 3: the two tails, via geom_tail_bound_cx at ratio 1/2 (binom_absorb).
  obtain ⟨C', hC'pos, hC'⟩ := binom_absorb S hS0
  have hdecay : ∀ j : ℕ, ‖hCoeff 1 j‖ ≤ C' * ((1:ℝ)/2) ^ j := by
    intro j
    refine le_trans (hd.dom_h j) ?_
    have hdj := dom_decay dom betaFam bHatOdd S hd j
    have h3pos : (0:ℝ) < (3:ℝ) ^ j := by positivity
    have hdom_le : dom j ≤ (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
      rw [le_mul_inv_iff₀ h3pos]
      linarith [hdj]
    exact le_trans hdom_le (hC' j)
  have htail1 := geom_tail_bound_cx (fun j => hCoeff 1 j) C' (1/2) (le_of_lt hC'pos)
    (by norm_num) (by norm_num) hdecay k
  -- the real-part tail is bounded by the complex tail
  -- STEP 3b: MAIN2's tail, at ratio 3/4 via binom_absorb_two.
  obtain ⟨C'', hC''pos, hC''⟩ := binom_absorb_two S hS0
  have hdecay2 : ∀ j : ℕ, ‖bHatOdd j * 2 ^ j‖ ≤ C'' * ((3:ℝ)/4) ^ j := by
    intro j
    rw [norm_mul, norm_pow]
    have h2n : ‖(2:ℂ)‖ = (2:ℝ) := by simp
    rw [h2n]
    have hb := hd.dom_b j
    have hdj := dom_decay dom betaFam bHatOdd S hd j
    have h3pos : (0:ℝ) < (3:ℝ) ^ j := by positivity
    have hdom_le : dom j ≤ (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
      rw [le_mul_inv_iff₀ h3pos]
      linarith [hdj]
    calc ‖bHatOdd j‖ * (2:ℝ) ^ j
        ≤ ((Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ))) * (2:ℝ) ^ j :=
          mul_le_mul_of_nonneg_right (le_trans hb hdom_le) (by positivity)
      _ ≤ C'' * ((3:ℝ)/4) ^ j := hC'' j
  have htail2 := geom_tail_bound_cx (fun j => bHatOdd j * 2 ^ j) C'' (3/4)
    (le_of_lt hC''pos) (by norm_num) (by norm_num) hdecay2 k
  -- the h_j(1) 2^j tail, same absorption at ratio 3/4
  have hdecay2h : ∀ j : ℕ, ‖hCoeff 1 j * 2 ^ j‖ ≤ C'' * ((3:ℝ)/4) ^ j := by
    intro j
    rw [norm_mul, norm_pow]
    have h2n : ‖(2:ℂ)‖ = (2:ℝ) := by simp
    rw [h2n]
    have hb := hd.dom_h j
    have hdj := dom_decay dom betaFam bHatOdd S hd j
    have h3pos : (0:ℝ) < (3:ℝ) ^ j := by positivity
    have hdom_le : dom j ≤ (Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
      rw [le_mul_inv_iff₀ h3pos]
      linarith [hdj]
    calc ‖hCoeff 1 j‖ * (2:ℝ) ^ j
        ≤ ((Nat.choose (j + 3) 3 : ℝ) * S * (3:ℝ) ^ (-(j:ℝ))) * (2:ℝ) ^ j :=
          mul_le_mul_of_nonneg_right (le_trans hb hdom_le) (by positivity)
      _ ≤ C'' * ((3:ℝ)/4) ^ j := hC'' j
  have htail2h := geom_tail_bound_cx (fun j => hCoeff 1 j * 2 ^ j) C'' (3/4)
    (le_of_lt hC''pos) (by norm_num) (by norm_num) hdecay2h k
  -- MAIN2's coefficient tail combines the two
  have htail2re : |∑' j : ℕ,
        (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant
          * (hCoeff 1 j).re) * 2 ^ j else 0)|
      ≤ C'' * ((3:ℝ)/4) ^ (k+1) / (1 - 3/4)
        + 2 * Real.eulerMascheroniConstant * (C'' * ((3:ℝ)/4) ^ (k+1) / (1 - 3/4)) := by
    have hg0 : (0:ℝ) < Real.eulerMascheroniConstant := by
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    -- the real tail is the real part of the complex tails
    have hcong : (∑' j : ℕ,
          (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant
            * (hCoeff 1 j).re) * 2 ^ j else 0))
        = (∑' j : ℕ, (if k < j then bHatOdd j * 2 ^ j else 0)).re
          + 2 * Real.eulerMascheroniConstant
            * (∑' j : ℕ, (if k < j then hCoeff 1 j * 2 ^ j else 0)).re := by
      have hsb : Summable (fun j : ℕ => (if k < j then bHatOdd j * 2 ^ j else 0)) := by
        apply Summable.of_norm_bounded (g := fun j : ℕ => ‖bHatOdd j * 2 ^ j‖)
          hsum2c.norm
        intro j
        by_cases hc : k < j <;> simp [hc]
      have hsh : Summable (fun j : ℕ => (if k < j then hCoeff 1 j * 2 ^ j else 0)) := by
        apply Summable.of_norm_bounded (g := fun j : ℕ => ‖hCoeff 1 j * 2 ^ j‖)
          hsum2h.norm
        intro j
        by_cases hc : k < j <;> simp [hc]
      rw [Complex.re_tsum hsb, Complex.re_tsum hsh, ← tsum_mul_left,
        ← Summable.tsum_add]
      · apply tsum_congr
        intro j
        by_cases hc : k < j
        · simp only [hc, if_true]
          have h2 : ((2:ℂ) ^ j) = (((2:ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
          rw [h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        · simp [hc]
      · apply Summable.congr (hsb.map (Complex.reCLM : ℂ →L[ℝ] ℝ) Complex.reCLM.continuous)
        intro j
        rfl
      · apply Summable.mul_left
        apply Summable.congr (hsh.map (Complex.reCLM : ℂ →L[ℝ] ℝ) Complex.reCLM.continuous)
        intro j
        rfl
    rw [hcong]
    refine le_trans (abs_add_le _ _) ?_
    apply add_le_add
    · exact le_trans (Complex.abs_re_le_norm _) htail2
    · rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.eulerMascheroniConstant)]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact le_trans (Complex.abs_re_le_norm _) htail2h
  -- STEP 4: the target equals |∫ D| up to the two tails.
  have hMain : |fOdd k - 1/2 - betaOdd * ((1:ℝ)/2) ^ k|
      ≤ |∫ u in Set.Ioi (0:ℝ),
            ((∑ j ∈ Finset.range (k + 1),
                (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
              * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
              - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u)|
        + |∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0)|
        + (1 / 2 ^ (k+1)) * |∑' j : ℕ,
            (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant
              * (hCoeff 1 j).re) * 2 ^ j else 0)| := by
    -- MAIN2's partial sum, like MAIN1's, is the full sum minus its tail
    have hpart2 : ∑ j ∈ Finset.range (k + 1), ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j
        = 2 * betaOdd - ∑' j : ℕ, (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0) := by
      have hlow : Summable (fun j : ℕ => (if j ≤ k then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0)) := by
        apply summable_of_finite_support
        apply Set.Finite.subset (Set.finite_Icc 0 k)
        intro j hj
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hj
        obtain ⟨hjk, _⟩ := hj
        exact ⟨Nat.zero_le j, hjk⟩
      have hhigh : Summable (fun j : ℕ => (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0)) := by
        apply Summable.of_norm_bounded (g := fun j : ℕ => |((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j|) hre2s.summable.abs
        intro j
        by_cases hc : k < j
        · simp only [hc, if_true, Real.norm_eq_abs]
          ring_nf
          exact le_refl _
        · simp only [hc, if_false, norm_zero]
          positivity
      have hsplitg : ∀ j : ℕ, ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j
          = (if j ≤ k then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0) + (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0) := by
        intro j
        by_cases hc : j ≤ k
        · simp [hc, Nat.not_lt.mpr hc]
        · simp [hc, Nat.lt_of_not_le hc]
      have htotal : (2 * betaOdd)
          = (∑' j : ℕ, (if j ≤ k then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0))
            + ∑' j : ℕ, (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0) := by
        have hsum := hre2s.tsum_eq
        conv_lhs => rw [← hsum]
        rw [← Summable.tsum_add hlow hhigh]
        exact tsum_congr hsplitg
      have hfin : (∑' j : ℕ, (if j ≤ k then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j else 0))
          = ∑ j ∈ Finset.range (k + 1), ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j := by
        rw [tsum_eq_sum (s := Finset.range (k + 1))]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          simp [Nat.lt_succ_iff.mp hj]
        · intro j hj
          rw [Finset.mem_range] at hj
          have hjk : ¬ (j ≤ k) := by omega
          simp [hjk]
      rw [hfin] at htotal
      linarith [htotal]
    have hbeta : betaOdd * ((1:ℝ)/2) ^ k
        = 1 / 2 ^ (k+1) * (2 * betaOdd) := by
      rw [div_pow, one_pow, pow_succ]
      field_simp
    have hid : fOdd k - 1/2 - betaOdd * ((1:ℝ)/2) ^ k
        = (∫ u in Set.Ioi (0:ℝ),
            ((∑ j ∈ Finset.range (k + 1),
                (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
              * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
              - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u))
          - (∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0))
          - (1 / 2 ^ (k+1)) * (∑' j : ℕ,
              (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant
                * (hCoeff 1 j).re) * 2 ^ j else 0)) := by
      rw [fOdd_u_form k hk hsum1 hsum hmul3 hcd1 hcd2, hsplit_int, hM1val, hM2val,
        hpart1, hpart2, hbeta]
      ring
    rw [hid]
    have hgen : ∀ (D A B c : ℝ), 0 ≤ c →
        |D - A - c * B| ≤ |D| + |A| + c * |B| := by
      intro D A B c hc
      have h1 : |D - A - c * B| ≤ |D - A| + |c * B| := by
        have := abs_add_le (D - A) (-(c * B))
        simpa [sub_eq_add_neg, abs_neg] using this
      have h2 : |D - A| ≤ |D| + |A| := by
        have := abs_add_le D (-A)
        simpa [sub_eq_add_neg, abs_neg] using this
      have h3 : |c * B| = c * |B| := by
        rw [abs_mul, abs_of_nonneg hc]
      linarith [h1, h2, h3.le, h3.ge]
    have := hgen
      (∫ u in Set.Ioi (0:ℝ),
        ((∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u))
      (∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0))
      (∑' j : ℕ, (if k < j then ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant
        * (hCoeff 1 j).re) * 2 ^ j else 0))
      ((1:ℝ) / 2 ^ (k+1)) (by positivity)
    linarith [this]


  have htail1re : |∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0)|
      ≤ C' * ((1:ℝ)/2) ^ (k+1) / (1 - 1/2) := by
    refine le_trans ?_ htail1
    have hcong : (∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0))
        = (∑' j : ℕ, (if k < j then hCoeff 1 j else 0)).re := by
      rw [Complex.re_tsum]
      · exact tsum_congr (fun j => by by_cases hc : k < j <;> simp [hc])
      · apply Summable.of_norm_bounded (g := fun j : ℕ => ‖hCoeff 1 j‖)
          hsummable1.norm
        intro j
        by_cases hc : k < j <;> simp [hc]
    rw [hcong]
    exact Complex.abs_re_le_norm _
  -- STEP 4b: split |int D| at U.
  have hDint := oddDiff_integrable dom betaFam bHatOdd S hf hd k hk hsum hmul3 hcd1 hcd2
  have hunion : Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) U ∪ Set.Ioi U := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx
      rcases lt_or_ge U x with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioc (0:ℝ) U) (Set.Ioi U) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    rw [Set.mem_Ioc] at hx
    rw [Set.mem_Ioi] at hx2
    linarith [hx.2, hx2]
  -- the integral splits across the union
  have hIocInt : MeasureTheory.IntegrableOn (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) (Set.Ioc (0:ℝ) U) := by
    apply hDint.mono_set
    rw [hunion]
    exact Set.subset_union_left
  have hIoiInt : MeasureTheory.IntegrableOn (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) (Set.Ioi U) := by
    apply hDint.mono_set
    rw [hunion]
    exact Set.subset_union_right
  have hsplitInt : (∫ u in Set.Ioi (0:ℝ), (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u)
      = (∫ u in Set.Ioc (0:ℝ) U, (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u)
        + ∫ u in Set.Ioi U, (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u := by
    rw [hunion]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIocInt hIoiInt
  -- FAR: |int_{Ioi U} D| <= CE * C(k+3,3) * S * 3^-(k+1)
  have hfarBound : |∫ u in Set.Ioi U, (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u|
      ≤ CE * (Nat.choose (k + 3) 3 : ℝ) * S * ((1:ℝ)/3) ^ (k + 1) := by
    have hnorm : |∫ u in Set.Ioi U, (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u|
        ≤ ∫ u in Set.Ioi U, |(fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
        - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u| := by
      have := MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict (Set.Ioi U))
        (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u)
      simpa [Real.norm_eq_abs] using this
    -- the majorant is integrable on Ioi U and dominates |D| there
    have hmajIoi0 : MeasureTheory.IntegrableOn
          (fun u : ℝ => CE * (∑ j ∈ Finset.range (k + 1),
            dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
          (Set.Ioi (0:ℝ)) := by
        have hrw : (fun u : ℝ => CE * (∑ j ∈ Finset.range (k + 1),
              dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
            = fun u : ℝ => ∑ j ∈ Finset.range (k + 1),
              (CE * dom j / (Nat.factorial (k - j))
                * (u ^ (k - j) * Real.exp (-(3 * u)))) := by
          funext u
          have h3u : (-3 : ℝ) * u = -(3 * u) := by ring
          rw [h3u, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hrw]
        apply MeasureTheory.integrable_finset_sum
        intro j _
        apply MeasureTheory.Integrable.const_mul
        have hgam : MeasureTheory.IntegrableOn
            (fun x : ℝ => Real.exp (-x) * x ^ (((k - j : ℕ) : ℝ) + 1 - 1)) (Set.Ioi 0) :=
          Real.GammaIntegral_convergent (by positivity)
        simp only [add_sub_cancel_right] at hgam
        have hgam' : MeasureTheory.IntegrableOn
            (fun x : ℝ => x ^ ((k - j : ℕ)) * Real.exp (-x)) (Set.Ioi 0) := by
          apply hgam.congr_fun _ measurableSet_Ioi
          intro x _
          simp only
          rw [← Real.rpow_natCast x (k - j)]
          ring
        apply MeasureTheory.Integrable.mono hgam'
        · apply MeasureTheory.AEStronglyMeasurable.mul <;>
            (apply Continuous.aestronglyMeasurable; fun_prop)
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : (0:ℝ) < x := hx
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos (Real.exp_pos (-(3*x))), abs_of_pos (Real.exp_pos (-x))]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp.mpr
          linarith
    have hmajInt : MeasureTheory.IntegrableOn
        (fun u : ℝ => CE * (∑ j ∈ Finset.range (k + 1),
          dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u))
        (Set.Ioi U) := by
      apply hmajIoi0.mono_set
      intro x hx
      exact lt_trans hUpos hx
    have habsInt : MeasureTheory.IntegrableOn (fun u : ℝ => |(fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u) u|) (Set.Ioi U) :=
      hIoiInt.abs
    refine le_trans hnorm ?_
    refine le_trans (MeasureTheory.setIntegral_mono_on habsInt hmajInt
      measurableSet_Ioi (fun u hu => ?_)) ?_
    · exact hsplitD u (le_of_lt hu)
    · have hfull := oddErr_integral_bound dom betaFam bHatOdd S CE (le_of_lt hCEpos) hd k
      refine le_trans ?_ hfull
      have hpull : (∫ x in Set.Ioi U,
            (CE * ∑ j ∈ Finset.range (k + 1),
              dom j * x ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * x))
          = CE * ∫ x in Set.Ioi U,
            (∑ j ∈ Finset.range (k + 1),
              dom j * x ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * x) := by
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _
        ring
      rw [hpull]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCEpos)
      apply MeasureTheory.setIntegral_mono_set
      · -- strip the CE factor from hmajIoi0
        have hCEne : CE ≠ 0 := ne_of_gt hCEpos
        have hsc : MeasureTheory.IntegrableOn
            (fun u : ℝ => CE⁻¹ * (CE * (∑ j ∈ Finset.range (k + 1),
              dom j * u ^ (k - j) / (Nat.factorial (k - j))) * Real.exp (-3 * u)))
            (Set.Ioi (0:ℝ)) :=
          MeasureTheory.Integrable.const_mul hmajIoi0 CE⁻¹
        apply hsc.congr_fun _ measurableSet_Ioi
        intro x _
        field_simp
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : (0:ℝ) < x := hx
        have hsumnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (k + 1),
            dom j * x ^ (k - j) / (Nat.factorial (k - j)) := by
          apply Finset.sum_nonneg
          intro j _
          have h1 := hd.dom_nonneg j
          have h2 : (0:ℝ) ≤ x ^ (k - j) := by positivity
          have h3 : (0:ℝ) < (Nat.factorial (k - j) : ℝ) := by
            exact_mod_cast Nat.factorial_pos (k - j)
          positivity
        have hexp : (0:ℝ) < Real.exp (-3 * x) := Real.exp_pos _
        exact mul_nonneg hsumnn (le_of_lt hexp)
      · exact MeasureTheory.ae_of_all _ (fun x hx => lt_trans hUpos hx)
  -- NEAR: |int_{Ioc 0 U} D| <= (leaf 3) + (MAIN1 near) + (MAIN2 near)
  have hSU : (1:ℝ) < sOf U := sOf_mem U hUpos
  have hnear3 := oddNear_integral_bound U hUpos k hk hsum hmul3 hcd1 hcd2
  have hnearM1 := oddSplitMain1_near dom betaFam bHatOdd S hd U hUpos k
  have hnearM2 := oddSplitMain2_near dom betaFam bHatOdd S hd U hUpos k
  have hM1IocInt : MeasureTheory.IntegrableOn (fun u : ℝ => oddSplitMain1 k u)
      (Set.Ioc (0:ℝ) U) := by
    have hc1 : Continuous (fun u : ℝ => oddSplitMain1 k u) := by
      unfold oddSplitMain1
      apply Continuous.mul _ (Real.continuous_exp.comp continuous_neg)
      apply continuous_finset_sum
      intro j _
      apply Continuous.div_const
      exact Continuous.mul continuous_const (continuous_pow _)
    exact hc1.integrableOn_Ioc
  have hM2IocInt : MeasureTheory.IntegrableOn (fun u : ℝ => oddSplitMain2 bHatOdd k u)
      (Set.Ioc (0:ℝ) U) := by
    have hc2 : Continuous (fun u : ℝ => oddSplitMain2 bHatOdd k u) := by
      unfold oddSplitMain2
      apply Continuous.mul _ (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))
      apply continuous_finset_sum
      intro j _
      apply Continuous.div_const
      exact Continuous.mul continuous_const (continuous_pow _)
    exact hc2.integrableOn_Ioc
  -- the near integral splits into the three pieces
  have hIintIoc : MeasureTheory.IntegrableOn
      (fun u : ℝ => (∑ j ∈ Finset.range (k + 1),
          (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
        * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
      (Set.Ioc (0:ℝ) U) := by
    have h := (hIocInt.add hM1IocInt).add hM2IocInt
    apply h.congr_fun _ measurableSet_Ioc
    intro u _
    simp only [Pi.add_apply]
    ring
  have hnearSplit : (∫ u in Set.Ioc (0:ℝ) U,
        ((∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u))
      = (∫ u in Set.Ioc (0:ℝ) U,
          (∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u))))
        - (∫ u in Set.Ioc (0:ℝ) U, oddSplitMain1 k u)
        - ∫ u in Set.Ioc (0:ℝ) U, oddSplitMain2 bHatOdd k u := by
    have e1 := MeasureTheory.integral_sub (hIintIoc.sub hM1IocInt) hM2IocInt
    have e2 := MeasureTheory.integral_sub hIintIoc hM1IocInt
    simp only [Pi.sub_apply] at e1
    rw [e2] at e1
    exact e1
  have hnearBound : |∫ u in Set.Ioc (0:ℝ) U,
        ((∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u)|
      ≤ FkOdd k (sOf U) / ((k:ℝ) * Real.log 3)
        + U * (∑ j ∈ Finset.range (k + 1),
            dom j * U ^ (k - j) / (Nat.factorial (k - j)))
        + U * ((1 + 2 * Real.eulerMascheroniConstant)
            * ∑ j ∈ Finset.range (k + 1),
                dom j * U ^ (k - j) / (Nat.factorial (k - j))) := by
    rw [hnearSplit]
    have htri : ∀ a b c : ℝ, |a - b - c| ≤ |a| + |b| + |c| := by
      intro a b c
      have h1 : |a - b - c| ≤ |a - b| + |c| := by
        have := abs_add_le (a - b) (-c)
        simpa [sub_eq_add_neg, abs_neg] using this
      have h2 : |a - b| ≤ |a| + |b| := by
        have := abs_add_le a (-b)
        simpa [sub_eq_add_neg, abs_neg] using this
      linarith [h1, h2]
    refine le_trans (htri _ _ _) ?_
    exact add_le_add (add_le_add hnear3 hnearM1) hnearM2
  -- STEP 5: collect.  The tails come straight from the certified inputs.
  have hA := ht.tail_h k
  have hB := ht.tail_b k
  have hkk : (0:ℝ) < ((k:ℝ) + 3) ^ 3 := by positivity
  have h3k : (0:ℝ) < ((1:ℝ)/3) ^ k := by positivity
  -- |A| <= (S0/2)(k+3)^3 (1/3)^k, since (k+3)^3 >= 1
  have hAb : |∑' j : ℕ, (if k < j then (hCoeff 1 j).re else 0)|
      ≤ (S0 / 2) * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    refine le_trans hA ?_
    have hone : (1:ℝ) ≤ ((k:ℝ) + 3) ^ 3 := by
      have hk3 : (1:ℝ) ≤ (k:ℝ) + 3 := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      first
      | exact one_le_pow₀ hk3
      | exact one_le_pow_of_le' hk3 3
      | nlinarith [hk3, sq_nonneg ((k:ℝ) + 3), mul_le_mul hk3 hk3 (by norm_num) (by linarith)]
    have hS0h : (0:ℝ) ≤ S0 / 2 := by linarith [ht.S0_nonneg]
    calc S0 / 2 * ((1:ℝ)/3) ^ k
        = (S0 / 2) * 1 * ((1:ℝ)/3) ^ k := by ring
      _ ≤ (S0 / 2) * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt h3k)
          exact mul_le_mul_of_nonneg_left hone hS0h
  -- 2^-(k+1)|B| <= (9 S1/128)(k+3)^3 (1/3)^k, using (k+2)/(k+3)^3 <= 3/64
  have hBb : (1 / 2 ^ (k+1)) * |∑' j : ℕ, (if k < j then
        ((bHatOdd j).re + 2 * Real.eulerMascheroniConstant * (hCoeff 1 j).re) * 2 ^ j
        else 0)|
      ≤ (5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64)
        * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    have h2k : (0:ℝ) < (1:ℝ) / 2 ^ (k+1) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hB (le_of_lt h2k)
    refine le_trans hstep ?_
    -- (1/2^(k+1)) * 3 S1 (k+2)(2/3)^k = (3 S1/2)(k+2)(1/3)^k
    have hcollapse : (1 / 2 ^ (k+1))
          * (2 * (S1 + 4 * Real.eulerMascheroniConstant * S0) * ((k:ℝ) + 4)
             * ((2:ℝ)/3) ^ k)
        = (S1 + 4 * Real.eulerMascheroniConstant * S0) * ((k:ℝ) + 4)
          * ((1:ℝ)/3) ^ k := by
      have hsp : ((2:ℝ)/3) ^ k = (2:ℝ) ^ k / 3 ^ k := by
        rw [div_pow]
      have hsp2 : ((1:ℝ)/3) ^ k = (1:ℝ) / 3 ^ k := by
        rw [div_pow, one_pow]
      rw [hsp, hsp2, pow_succ]
      have h2 : (2:ℝ) ^ k ≠ 0 := by positivity
      have h3 : (3:ℝ) ^ k ≠ 0 := by positivity
      field_simp
    rw [hcollapse]
    -- (k+2) <= (3/64)(k+3)^3, tight at k = 1
    have hpoly : ((k:ℝ) + 4) ≤ (5/64) * (((k:ℝ) + 3) ^ 3) := by
      have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      nlinarith [hk1, sq_nonneg ((k:ℝ) - 1), sq_nonneg ((k:ℝ) + 3),
        mul_nonneg (sub_nonneg.mpr hk1) (sq_nonneg ((k:ℝ) + 3))]
    have hS1h : (0:ℝ) ≤ S1 + 4 * Real.eulerMascheroniConstant * S0 :=
      ht.Bnorm_nonneg
    have h3k' : (0:ℝ) < ((1:ℝ)/3) ^ k := by positivity
    calc (S1 + 4 * Real.eulerMascheroniConstant * S0) * ((k:ℝ) + 4) * ((1:ℝ)/3) ^ k
        ≤ (S1 + 4 * Real.eulerMascheroniConstant * S0) * ((5/64) * (((k:ℝ) + 3) ^ 3)) * ((1:ℝ)/3) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt h3k')
          exact mul_le_mul_of_nonneg_left hpoly hS1h
      _ = (5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64)
            * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by ring
  -- collect: hMain, hsplitInt, hfarBound, hnearBound, hAb, hBb against hMR
  rw [fOdd_u_form k hk hsum1 hsum hmul3 hcd1 hcd2] at hMain
  refine le_trans hMain ?_
  -- bound the integral term by far + near
  have hInt : |∫ u in Set.Ioi (0:ℝ),
        ((∑ j ∈ Finset.range (k + 1),
            (hCoeff (sOf u) j).re * u ^ (k - j) / (Nat.factorial (k - j)))
          * ((∑' n : ℕ, ((n:ℝ) + 1) ^ (-(sOf u))) / (-zetaRderiv (sOf u)))
          - oddSplitMain1 k u - oddSplitMain2 bHatOdd k u)|
      ≤ (FkOdd k (sOf U) / ((k:ℝ) * Real.log 3)
          + U * (∑ j ∈ Finset.range (k + 1),
              dom j * U ^ (k - j) / (Nat.factorial (k - j)))
          + U * ((1 + 2 * Real.eulerMascheroniConstant)
              * ∑ j ∈ Finset.range (k + 1),
                  dom j * U ^ (k - j) / (Nat.factorial (k - j))))
        + CE * (Nat.choose (k + 3) 3 : ℝ) * S * ((1:ℝ)/3) ^ (k + 1) := by
    rw [hsplitInt]
    refine le_trans (abs_add_le _ _) ?_
    exact add_le_add hnearBound hfarBound
  refine le_trans (add_le_add (add_le_add hInt hAb) hBb) ?_
  have hP : (0:ℝ) < ((1:ℝ)/3) ^ k := by positivity
  have hXpos : (0:ℝ) < (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by positivity
  have hFk : FkOdd k (sOf U) / ((k:ℝ) * Real.log 3)
      ≤ CN * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    have hFnn : (0:ℝ) ≤ FkOdd k (sOf U) := by
      unfold FkOdd; apply tsum_nonneg; intro n; positivity
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hl3 : (1:ℝ) ≤ Real.log 3 := by
      have he : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have := Real.log_lt_log (Real.exp_pos 1) he
      rw [Real.log_exp] at this
      linarith
    have hlog1 : (1:ℝ) ≤ (k:ℝ) * Real.log 3 := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (k:ℝ) * Real.log 3 := mul_le_mul hk1 hl3 (by norm_num) (by linarith)
    have hone : (1:ℝ) ≤ ((k:ℝ) + 3) ^ 3 := by
      have hk3 : (1:ℝ) ≤ (k:ℝ) + 3 := by linarith
      first
      | exact one_le_pow₀ hk3
      | nlinarith [hk3]
    calc FkOdd k (sOf U) / ((k:ℝ) * Real.log 3)
        ≤ FkOdd k (sOf U) := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < (k:ℝ) * Real.log 3)]
          nlinarith [hFnn, hlog1]
      _ ≤ CN * ((1:ℝ)/3) ^ k := hCN
      _ = CN * 1 * ((1:ℝ)/3) ^ k := by ring
      _ ≤ CN * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hP)
          exact mul_le_mul_of_nonneg_left hone hCNnn
  have hnearU : U * (∑ j ∈ Finset.range (k + 1),
        dom j * U ^ (k - j) / (Nat.factorial (k - j)))
      + U * ((1 + 2 * Real.eulerMascheroniConstant)
          * ∑ j ∈ Finset.range (k + 1),
              dom j * U ^ (k - j) / (Nat.factorial (k - j)))
      ≤ NEARU * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    refine le_trans ?_ hNEARU
    have he : U * (2 + 2 * Real.eulerMascheroniConstant)
        * (∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j)))
        = U * (∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j)))
          + U * ((1 + 2 * Real.eulerMascheroniConstant)
              * ∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j))) := by
      ring
    linarith [he]
  have hfar : CE * (Nat.choose (k + 3) 3 : ℝ) * S * ((1:ℝ)/3) ^ (k + 1)
      ≤ (CE * S / 18) * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    have hbin : (Nat.choose (k + 3) 3 : ℝ) ≤ ((k:ℝ) + 3) ^ 3 / 6 := by
      rw [choose_three_real]
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      have hfac : ((k:ℝ) + 3) * ((k:ℝ) + 2) * ((k:ℝ) + 1)
          ≤ ((k:ℝ) + 3) * ((k:ℝ) + 3) * ((k:ℝ) + 3) := by
        have h2 : (k:ℝ) + 2 ≤ (k:ℝ) + 3 := by linarith
        have h1 : (k:ℝ) + 1 ≤ (k:ℝ) + 3 := by linarith
        have hp : (0:ℝ) ≤ (k:ℝ) + 3 := by linarith
        nlinarith [h1, h2, hp]
      have hcube : ((k:ℝ) + 3) ^ 3
          = ((k:ℝ) + 3) * ((k:ℝ) + 3) * ((k:ℝ) + 3) := by ring
      rw [hcube]
      linarith [hfac]
    have hsucc : ((1:ℝ)/3) ^ (k + 1) = ((1:ℝ)/3) ^ k * (1/3) := pow_succ _ _
    rw [hsucc]
    calc CE * (Nat.choose (k + 3) 3 : ℝ) * S * (((1:ℝ)/3) ^ k * (1/3))
        ≤ CE * (((k:ℝ) + 3) ^ 3 / 6) * S * (((1:ℝ)/3) ^ k * (1/3)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hS0
          exact mul_le_mul_of_nonneg_left hbin (le_of_lt hCEpos)
      _ = (CE * S / 18) * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by ring
  have hsum : FkOdd k (sOf U) / ((k:ℝ) * Real.log 3)
        + U * (∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j)))
        + U * ((1 + 2 * Real.eulerMascheroniConstant)
            * ∑ j ∈ Finset.range (k + 1), dom j * U ^ (k - j) / (Nat.factorial (k - j)))
        + CE * (Nat.choose (k + 3) 3 : ℝ) * S * ((1:ℝ)/3) ^ (k + 1)
        + S0 / 2 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
        + 5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      ≤ CN * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
        + NEARU * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
        + CE * S / 18 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
        + S0 / 2 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
        + 5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := by
    linarith [hFk, hnearU, hfar]
  refine le_trans hsum ?_
  have hK : (0:ℝ) ≤ (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k := le_of_lt hXpos
  have hexp : CN * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      + NEARU * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      + CE * S / 18 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      + S0 / 2 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      + 5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64 * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      = (CN + NEARU + CE * S / 18 + S0 / 2
          + 5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64) * ((((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k) := by ring
  rw [hexp]
  have hfin : MR * (((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k
      = MR * ((((k:ℝ) + 3) ^ 3) * ((1:ℝ)/3) ^ k) := by ring
  rw [hfin]
  have hcombine : CN + NEARU + CE * S / 18 + S0 / 2 + 5 * (S1 + 4 * Real.eulerMascheroniConstant * S0) / 64 ≤ MR := by
    linarith [hMR]
  exact mul_le_mul_of_nonneg_right hcombine hK









