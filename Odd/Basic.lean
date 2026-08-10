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
derived bound.  Supplied here by odd/numerics/mr_certified.py, whose interval
sweep ranges over s in [1,2] as well as the z-circle. -/
structure OddCoeffFacts (betaS : ℝ) : Prop where
  nonneg : 0 ≤ betaS
  deriv_exists : ∀ j : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
    HasDerivAt (fun t : ℝ => hCoeff t j) (deriv (fun t : ℝ => hCoeff t j) x) x
  deriv_bound : ∀ j : ℕ, ∀ x ∈ Set.Ioo (1:ℝ) 2,
    ‖deriv (fun t : ℝ => hCoeff t j) x‖ ≤ betaS
  /-- The coefficients converge to their s = 1 values from the right.

  Certified alongside the derivative bound by the same interval sweep; the
  main development's `gManu_tendsto_cCoeff` is the analogue. -/
  tendsto_one : ∀ j : ℕ, Filter.Tendsto (fun t : ℝ => hCoeff t j)
    (nhdsWithin 1 (Set.Ioi (1:ℝ))) (nhds (hCoeff 1 j))

/-- The mean-value step: |h_j(s) - h_j(t)| <= betaS |s - t| on (1,2),
uniformly in j.  Transferred from gManu_lipschitz_interior. -/
theorem hCoeff_lipschitz (betaS : ℝ) (hf : OddCoeffFacts betaS) (j : ℕ)
    (t s : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 2) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    ‖hCoeff s j - hCoeff t j‖ ≤ betaS * ‖s - t‖ := by
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

/-- The near-pole integral of the expansion, term by term. -/
theorem fOdd_near_integral (k : ℕ) (hk : 1 ≤ k)
    (hsum : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Summable (fun n : ℕ => ‖zOmegaHom s z n‖))
    (hmul3 : ∀ s : ℝ, 1 < s → ∀ z : ℂ, ‖z‖ ≤ 2 →
      Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - zOmegaHom s z (p : ℕ))⁻¹))
    (hcd1 : ∀ s : ℝ, 1 < s →
      ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Complex.exp ((uOf s : ℂ) * z)) 0)
    (hcd2 : ∀ s : ℝ, 1 < s → ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => Hodd s z) 0)
    (B : ℝ) (hB : ∀ j : ℕ, ∀ s : ℝ, 1 < s → s ≤ 2 → ‖hCoeff s j‖ ≤ B) :
    (∫ u in Set.Ioi (0:ℝ), FkOdd k (1 + Real.exp (-u)) * Real.exp (-u))
      = ∑ j ∈ Finset.range (k + 1),
          ∫ u in Set.Ioi (0:ℝ),
            (hCoeff (1 + Real.exp (-u)) j).re
              * (uOf (1 + Real.exp (-u))) ^ (k - j) / (Nat.factorial (k - j))
              * Real.exp (-u) := by
  -- SUPERSEDED: this route needs |uOf(1+e^-x)| <= x, which is false.
  -- The correct organisation substitutes u = log zeta(s) directly;
  -- see substitution_log_zeta below.
  sorry

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
    rw [hexpu u hu0, ← hone]
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

/-- STEP B: the coefficients at s(u) differ from those at 1 by O(e^-u),
uniformly in j.

Composes hCoeff_lipschitz (|h_j(s) - h_j(t)| <= betaS |s - t|) with
eps_of_u_bound (s(u) - 1 <= C e^-u).  Note h_j(1) is the limiting value; the
Lipschitz bound is stated on (1,2), so this is |h_j(s(u)) - h_j(1+delta)| for
delta small, and h_j(1) enters as the limit. -/
theorem hCoeff_sub_one_bound (betaS : ℝ) (hf : OddCoeffFacts betaS) (j : ℕ)
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    ‖hCoeff s j - hCoeff 1 j‖ ≤ betaS * (s - 1) :=
  deriv_sub_limit_bound (fun t => hCoeff t j) (hCoeff 1 j) betaS hf.nonneg
    (fun x hx => hf.deriv_exists j x hx) (fun x hx => hf.deriv_bound j x hx)
    (hf.tendsto_one j) s hs

theorem hCoeff_u_form (betaS : ℝ) (hf : OddCoeffFacts betaS) (j : ℕ) :
    ∃ C > 0, ∃ U > 0, ∀ u : ℝ, U ≤ u →
      ‖hCoeff (sOf u) j - hCoeff 1 j‖ ≤ C * Real.exp (-u) := by
  sorry
