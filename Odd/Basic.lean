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
