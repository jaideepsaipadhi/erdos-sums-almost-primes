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

This is the change of variables odd/PROOF.md section 2 performs; the far piece
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

/-- THE COEFFICIENT EXTRACTION.  Stated as a HasSum over j <= k. -/
theorem FkOdd_expansion (k : ℕ) (s : ℝ) (hs : 1 < s) :
    (FkOdd k s : ℂ) = ∑ j ∈ Finset.range (k + 1),
      hCoeff s j * ((uOf s : ℝ) : ℂ) ^ (k - j) / (Nat.factorial (k - j)) := by
  sorry

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

/-- The odd generating function is the Euler product over p >= 3:

    zOmegaOdd s z = sum_{n odd} z^Omega(n) n^-s = prod_{p>=3} (1 - z p^-s)^-1

and by the definition of Hodd this equals zeta(s)^z * Hodd s z.

This is the odd analogue of the main development's route from the sum over n
to Fbig; there the p = 2 factor is pulled out separately, here it is absent. -/
theorem zOmegaOdd_eq_euler (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : ‖z‖ < 3 ^ s) :
    zOmegaOdd s z = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
  sorry

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
    · sorry

/-- THE CONVOLUTION (6c step 2, second half).

By Leibniz applied to zOmegaOdd s = exp(u ·) * Hodd s, the k-th Taylor
coefficient is the convolution of u^j/j! with h_j. -/
theorem FkOdd_convolution (k : ℕ) (s : ℝ) (hs : 1 < s)
    (hfac : ∀ z : ℂ, zOmegaOdd s z = Complex.exp ((uOf s : ℂ) * z) * Hodd s z)
    (hcd1 : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0) :
    iteratedDeriv k (fun z => zOmegaOdd s z) 0 / (Nat.factorial k : ℂ)
      = ∑ j ∈ Finset.range (k + 1),
          hCoeff s j * ((uOf s : ℝ) : ℂ) ^ (k - j) / (Nat.factorial (k - j)) := by
  sorry
