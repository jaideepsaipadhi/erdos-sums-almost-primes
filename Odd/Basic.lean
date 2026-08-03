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

THE PROOF (odd/PROOF.md, derived and verified 2026-08-01):

  f_k^odd = 1/2 + beta 2^-k + R_k,   beta = d (log 2 - S + gamma) = 0.15563

with S = sum_{p>=3} log p/((p-1)(p-2)), and |R_k| <= M_R R^-k by Cauchy on
|z| = R < 5 applied to Htilde(s,z) = H(s,z)(1 - z 3^-s).  With M_R <= 826.71
at R = 4.5 the inequality holds for k >= 12; k = 1..11 is certified directly.

THE STRUCTURAL POINT.  H(s,z) = (1-2^-s)^z prod_{p>=3}(1-z p^-s)^-1(1-p^-s)^z
is analytic in |z| < 3^s, so z = 2 lies strictly INSIDE.  In the unrestricted
problem the corresponding function is analytic only in |z| < 2^s and z = 2 is
ON the boundary -- that is what produces the k^2 competing with 2^-k, hence
the turnaround at k = 6 and all of sections 4-7 of the main development.

Numerics in odd/README.md: f_k^odd certified for k = 1..20, strictly
decreasing, tending to 1/2 from above.
-/

open Real BigOperators
noncomputable section

/-- The Erdos sum restricted to odd n. -/
def fOdd (k : ℕ) : ℝ :=
  ∑' n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}, 1 / ((n : ℝ) * Real.log n)

-- The limit f_k^odd -> 1/2 is derived in odd/PROOF.md section 3 (it is
-- H(1,1) = 1 - 2^-1, the omitted Euler factor at z = s = 1) and confirmed
-- numerically to k = 20.  It is not formalized here because the decreasing
-- theorem does not use it.



/-- S = sum over odd primes of log p / ((p-1)(p-2)).

Certified enclosure [0.8593920314, 0.8593986014]: head to 5e6 plus the tail
bound sum_{n>P} 2 log n / n^2 < 2(log P + 1)/P. -/
noncomputable def Sodd : ℝ := ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
  Real.log p / (((p : ℝ) - 1) * ((p : ℝ) - 2))

/-- The leading coefficient of the odd expansion,
beta = d (log 2 - S + gamma), numerically 0.15563. -/
noncomputable def betaOdd : ℝ :=
  dConst * (Real.log 2 - Sodd + Real.eulerMascheroniConstant)

/-- The certified inputs the odd theorem assumes.

As in the main development these are Arb ball computations, not formalized
results.  `Sodd_enclosure` and `MR_bound` come from odd/numerics/, `d` is
already certified in Banksmartin.Basic, and `sweep_low` is the certified
sweep over the range below the analytic threshold. -/
structure OddNumericalFacts (MR : ℝ) : Prop where
  /-- The certified enclosure of S. -/
  Sodd_enclosure : |Sodd - 0.8593953| ≤ 3.3e-6
  /-- Cauchy bound: the sup of |Htilde| on |z| = 4.5, s in [1,2]. -/
  MR_bound       : MR ≤ 826.705058
  /-- The remainder bound that Cauchy's estimate yields. -/
  remainder      : ∀ k : ℕ, |fOdd k - 1 / 2 - betaOdd * ((1:ℝ)/2) ^ k|
                     ≤ MR * ((2:ℝ)/9) ^ k
  /-- Certified sweep below the analytic threshold. -/
  sweep_low      : ∀ k : ℕ, 1 ≤ k → k ≤ 11 → fOdd (k + 1) < fOdd k
  /-- Euler-Mascheroni, lower bound.  Mathlib has
  `eulerMascheroniConstant_lt_two_thirds` but no lower bound, so this enters as
  an input.  It is a Mathlib gap, not a mathematical one. -/
  gamma_gt       : (0.5772156 : ℝ) < Real.eulerMascheroniConstant
  /-- The certified enclosure of d, from the main development. -/
  d_enc          : |dConst - 0.3786950| ≤ 5.3e-8
/-- The arithmetic core of the odd assembly, with all rpow stripped out.

A = f_k, B = f_{k+1}, P = 2^-k, T = MR 2^-k (4/9)^k, b = beta.  The two
enclosures give A >= bP - T and B <= bP/2 + 2T/9, so
A - B >= bP/2 - T(11/9) >= P(0.1556/2 - 0.06002*11/9) = 0.00444 P > 0. -/
theorem odd_step (b P T A B : ℝ)
    (hb : (0.1556 : ℝ) ≤ b) (hP : 0 < P) (hT : 0 ≤ T)
    (hTb : T ≤ (0.06002 : ℝ) * P)
    (hA : |A - b * P| ≤ T)
    (hB : |B - b * P / 2| ≤ T * (2/9)) :
    B < A := by
  have hA1 := (abs_le.mp hA).1
  have hB2 := (abs_le.mp hB).2
  nlinarith [hA1, hB2, hTb, hP, hT, hb]

/-- The odd theorem, conditional on the certified inputs.

For k >= 12 the leading term beta 2^-k dominates the Cauchy-bounded remainder;
below that the certified sweep covers it.  See odd/PROOF.md section 6. -/
theorem fOdd_decreasing_of_facts (MR : ℝ) (hMR0 : 0 ≤ MR)
    (hnum : OddNumericalFacts MR) :
    ∀ k : ℕ, 1 ≤ k → fOdd (k + 1) < fOdd k := by
  intro k hk
  by_cases hsmall : k ≤ 11
  · exact hnum.sweep_low k hk hsmall
  · have hk12 : 12 ≤ k := by omega
    set P : ℝ := ((1:ℝ)/2) ^ k with hPdef
    have hP : 0 < P := pow_pos (by norm_num) k
    set T : ℝ := MR * ((2:ℝ)/9) ^ k with hTdef
    have hT : 0 ≤ T := by
      rw [hTdef]; exact mul_nonneg hMR0 (pow_nonneg (by norm_num) k)
    -- (2/9)^k = (4/9)^k (1/2)^k, and (4/9)^k ≤ (4/9)^12
    have hfac : ((2:ℝ)/9) ^ k = ((4:ℝ)/9) ^ k * ((1:ℝ)/2) ^ k := by
      rw [← mul_pow]; norm_num
    have hmono : ((4:ℝ)/9) ^ k ≤ ((4:ℝ)/9) ^ 12 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk12
    have hTb : T ≤ (0.06002:ℝ) * P := by
      rw [hTdef, hfac, hPdef]
      have h1 : MR * (((4:ℝ)/9) ^ k * ((1:ℝ)/2) ^ k)
          ≤ MR * (((4:ℝ)/9) ^ 12 * ((1:ℝ)/2) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hMR0
        exact mul_le_mul_of_nonneg_right hmono (pow_nonneg (by norm_num) k)
      have h2 : MR * (((4:ℝ)/9) ^ 12 * ((1:ℝ)/2) ^ k)
          ≤ (826.705058:ℝ) * (((4:ℝ)/9) ^ 12 * ((1:ℝ)/2) ^ k) := by
        apply mul_le_mul_of_nonneg_right hnum.MR_bound
        positivity
      have h3 : (826.705058:ℝ) * ((4:ℝ)/9) ^ 12 ≤ (0.06002:ℝ) := by
        norm_num
      nlinarith [h1, h2, h3, pow_pos (show (0:ℝ) < 1/2 by norm_num) k]
    have hb : (0.1556 : ℝ) ≤ betaOdd := by
      unfold betaOdd
      have hg := hnum.gamma_gt
      have hd := abs_le.mp hnum.d_enc
      have hS := abs_le.mp hnum.Sodd_enclosure
      have hl2 := Real.log_two_gt_d9
      nlinarith [hg, hd.1, hd.2, hS.1, hS.2, hl2]
    have hA : |(fOdd k - 1/2) - betaOdd * P| ≤ T := by
      rw [hPdef, hTdef]
      have := hnum.remainder k
      calc |(fOdd k - 1/2) - betaOdd * ((1:ℝ)/2) ^ k|
          = |fOdd k - 1/2 - betaOdd * ((1:ℝ)/2) ^ k| := by ring_nf
        _ ≤ MR * ((2:ℝ)/9) ^ k := this
    have hB : |(fOdd (k+1) - 1/2) - betaOdd * P / 2| ≤ T * (2/9) := by
      have h := hnum.remainder (k+1)
      have e1 : ((1:ℝ)/2) ^ (k+1) = ((1:ℝ)/2) ^ k / 2 := by
        rw [pow_succ]; ring
      have e2 : ((2:ℝ)/9) ^ (k+1) = ((2:ℝ)/9) ^ k * (2/9) := by
        rw [pow_succ]
      rw [e1, e2] at h
      rw [hPdef, hTdef]
      calc |(fOdd (k+1) - 1/2) - betaOdd * ((1:ℝ)/2) ^ k / 2|
          = |fOdd (k+1) - 1/2 - betaOdd * (((1:ℝ)/2) ^ k / 2)| := by ring_nf
        _ ≤ MR * ((2:ℝ)/9) ^ k * (2/9) := by
              calc |fOdd (k+1) - 1/2 - betaOdd * (((1:ℝ)/2) ^ k / 2)|
                  ≤ MR * (((2:ℝ)/9) ^ k * (2/9)) := h
                _ = MR * ((2:ℝ)/9) ^ k * (2/9) := by ring
    have := odd_step betaOdd P T (fOdd k - 1/2) (fOdd (k+1) - 1/2)
      hb hP hT hTb hA hB
    linarith [this]

/-- THE ODD THEOREM, conditional on the certified inputs -- exactly as
`erdos_sums_increase_from_six` is conditional on `NumericalFacts`.

`OddNumericalFacts` assumes the analytic content of odd/PROOF.md sections 2-5:
the expansion f_k^odd = 1/2 + beta 2^-k + R_k and the Cauchy bound
|R_k| <= MR (2/9)^k.  What is proved here is section 6, the assembly. -/
theorem fOdd_decreasing (MR : ℝ) (hMR0 : 0 ≤ MR) (hnum : OddNumericalFacts MR) :
    ∀ k : ℕ, 1 ≤ k → fOdd (k + 1) < fOdd k :=
  fOdd_decreasing_of_facts MR hMR0 hnum

end

/-- H(s,z), the regularised odd Euler product:

    H(s,z) = (1 - 2^-s)^z * prod_{p>=3} (1 - z p^-s)^-1 (1 - p^-s)^z

so that prod_{p>=3}(1 - z p^-s)^-1 = zeta(s)^z H(s,z).  Analytic in |z| < 3^s;
this is the function whose values at z = 1 and z = 2 give the limit 1/2 and
the leading coefficient.  See odd/PROOF.md section 2. -/
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
limit comes from -- the omitted Euler factor at z = s = 1.  See odd/PROOF.md
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
term for term by Hodd_factor_at_two.  See odd/PROOF.md section 4. -/
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
odd/PROOF.md section 5. -/
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

/-- Cauchy's coefficient estimate, in the form odd/PROOF.md section 5 uses:
if f is analytic on the closed ball of radius R and bounded by C on the
sphere, its Taylor coefficients at 0 satisfy |a_k| <= C / R^k.

This is the shape of the remainder bound; the value of C for Htilde is the
certified interval computation (odd/numerics/mr_certified.py) and stays an
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
