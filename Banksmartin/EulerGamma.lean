import Mathlib

/-!
# Euler's integral for the Euler-Mascheroni constant (SCAFFOLD)

Target: `gamma = - int_{u > 0} exp(-u) * log u du`, needed for the upper bound
of manuscript Theorem 4.1 (the gap-5 evaluation).

Pin recon (2026-07-25): `Real.eulerMascheroniConstant` occurs ONLY in
Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean, where `digamma = logDeriv Gamma`
and `digamma_one : digamma 1 = -eulerMascheroniConstant`. There is NO
derivative-under-the-integral lemma for Gamma in the pin. So the bridge must be built:

    Gamma'(1) = digamma 1 * Gamma 1 = -gamma          (from the pin)
    Gamma'(s) = int_{u>0} exp(-u) u^(s-1) log u du    (TO BUILD: differentiate
                                                      under the integral sign)

then evaluate at s = 1.

Strategy for the middle step, on a neighbourhood s in (1/2, 3/2):
  * pointwise derivative: d/ds [u^(s-1)] = u^(s-1) * log u  (Real.rpow, u > 0)
  * dominating function for the s-derivative, uniform on (1/2, 3/2):
        F(u) = exp(-u) * (u^(-1/2) + u^(1/2)) * |log u|
    which is integrable on (0, infty): near 0 the u^(-1/2)|log u| factor is
    integrable; at infinity exp(-u) dominates any power times log.
  * invoke `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

Each `sorry` below is a separate, self-contained obligation.
-/

open MeasureTheory Real

namespace BanksMartin

/-- The dominating function used for differentiation under the integral sign. -/
noncomputable def gammaDeriv_dom (u : ℝ) : ℝ :=
  Real.exp (-u) * (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2)) * |Real.log u|

/-- Near zero: |log u| is dominated by a small negative power. -/
theorem abs_log_le_rpow_near_zero (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    |Real.log u| ≤ 4 * u ^ (-(1:ℝ)/4) := by
  have hx : (0:ℝ) < u ^ (-(1:ℝ)/4) := Real.rpow_pos_of_pos hu _
  have hlogx : Real.log (u ^ (-(1:ℝ)/4)) = (-(1:ℝ)/4) * Real.log u :=
    Real.log_rpow hu _
  have hle := Real.log_le_sub_one_of_pos hx
  rw [hlogx] at hle
  have hnonpos : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1
  rw [abs_of_nonpos hnonpos]
  linarith

/-- Far out: |log u| is dominated by u itself. -/
theorem abs_log_le_self (u : ℝ) (hu : 1 ≤ u) :
    |Real.log u| ≤ u := by
  have hpos : (0:ℝ) < u := by linarith
  have hnonneg : 0 ≤ Real.log u := Real.log_nonneg hu
  rw [abs_of_nonneg hnonneg]
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Obligation 1, near-zero half. -/
theorem gammaDeriv_dom_integrableOn_Ioo :
    IntegrableOn gammaDeriv_dom (Set.Ioo 0 1) := by
  have hb1 : IntegrableOn (fun u : ℝ => u ^ (-(3:ℝ)/4)) (Set.Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)]
    norm_num
  have hb2 : IntegrableOn (fun u : ℝ => u ^ ((1:ℝ)/4)) (Set.Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)]
    norm_num
  have hbound : IntegrableOn
      (fun u : ℝ => 4 * u ^ (-(3:ℝ)/4) + 4 * u ^ ((1:ℝ)/4))
      (Set.Ioo 0 1) := (hb1.const_mul 4).add (hb2.const_mul 4)
  apply MeasureTheory.Integrable.mono hbound
  · unfold gammaDeriv_dom
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
    obtain ⟨hu0, hu1⟩ := hu
    unfold gammaDeriv_dom
    have hA : (0:ℝ) < u ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
    have hB : (0:ℝ) < u ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
    have hE : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hL : |Real.log u| ≤ 4 * u ^ (-(1:ℝ)/4) :=
      abs_log_le_rpow_near_zero u hu0 hu1.le
    have hM1 : u ^ (-(1:ℝ)/2) * (4 * u ^ (-(1:ℝ)/4))
        = 4 * u ^ (-(3:ℝ)/4) := by
      rw [show (4:ℝ) * u ^ (-(1:ℝ)/4) = u ^ (-(1:ℝ)/4) * 4 by ring,
        ← mul_assoc, ← Real.rpow_add hu0]
      norm_num
      ring
    have hM2 : u ^ ((1:ℝ)/2) * (4 * u ^ (-(1:ℝ)/4))
        = 4 * u ^ ((1:ℝ)/4) := by
      rw [show (4:ℝ) * u ^ (-(1:ℝ)/4) = u ^ (-(1:ℝ)/4) * 4 by ring,
        ← mul_assoc, ← Real.rpow_add hu0]
      norm_num
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * u ^ (-(3:ℝ)/4) + 4 * u ^ ((1:ℝ)/4))]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤
      Real.exp (-u) * (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2)) * |Real.log u|)]
    calc Real.exp (-u) * (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2)) * |Real.log u|
        ≤ 1 * (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2)) * (4 * u ^ (-(1:ℝ)/4)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hE (by positivity)) hL (abs_nonneg _)
          positivity
      _ = u ^ (-(1:ℝ)/2) * (4 * u ^ (-(1:ℝ)/4))
          + u ^ ((1:ℝ)/2) * (4 * u ^ (-(1:ℝ)/4)) := by ring
      _ = 4 * u ^ (-(3:ℝ)/4) + 4 * u ^ ((1:ℝ)/4) := by rw [hM1, hM2]

/-- Obligation 1, tail half: on [1, infty) the dominating function is bounded
by 2 exp(-u) u^(3/2), which is a Gamma integrand. -/
theorem gammaDeriv_dom_integrableOn_Ici :
    IntegrableOn gammaDeriv_dom (Set.Ici 1) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ ((3:ℝ)/2)) (Set.Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := (5:ℝ)/2) (by norm_num)
    apply h.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only
    rw [show (5:ℝ)/2 - 1 = (3:ℝ)/2 by ring]
  have hsub : Set.Ici (1:ℝ) ⊆ Set.Ioi 0 := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_Ioi]
    linarith
  have hbound : IntegrableOn
      (fun u : ℝ => 2 * (Real.exp (-u) * u ^ ((3:ℝ)/2))) (Set.Ici 1) :=
    (hg.mono hsub le_rfl).const_mul 2
  apply MeasureTheory.Integrable.mono hbound
  · unfold gammaDeriv_dom
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with u hu
    have hu1 : (1:ℝ) ≤ u := hu
    have hu0 : (0:ℝ) < u := by linarith
    unfold gammaDeriv_dom
    have hE : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
    have hA : (0:ℝ) < u ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
    have hB : (0:ℝ) < u ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
    have hL : |Real.log u| ≤ u := abs_log_le_self u hu1
    have hAle : u ^ (-(1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) := by
      apply Real.rpow_le_rpow_of_exponent_le hu1
      norm_num
    have hprod : u ^ ((1:ℝ)/2) * u = u ^ ((3:ℝ)/2) := by
      have h1 : u ^ ((1:ℝ)/2) * u ^ (1:ℝ) = u ^ ((3:ℝ)/2) := by
        rw [← Real.rpow_add hu0]
        norm_num
      rwa [Real.rpow_one] at h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤
      2 * (Real.exp (-u) * u ^ ((3:ℝ)/2)))]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤
      Real.exp (-u) * (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2)) * |Real.log u|)]
    calc Real.exp (-u) * (u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2)) * |Real.log u|
        ≤ Real.exp (-u) * (u ^ ((1:ℝ)/2) + u ^ ((1:ℝ)/2)) * u := by
          apply mul_le_mul _ hL (abs_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hE.le
          linarith
      _ = 2 * (Real.exp (-u) * (u ^ ((1:ℝ)/2) * u)) := by ring
      _ = 2 * (Real.exp (-u) * u ^ ((3:ℝ)/2)) := by rw [hprod]

/-- OBLIGATION 1: the dominating function is integrable on (0, infty). -/
theorem gammaDeriv_dom_integrable :
    IntegrableOn gammaDeriv_dom (Set.Ioi 0) := by
  have hsplit : Set.Ioo (0:ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 :=
    Set.Ioo_union_Ici_eq_Ioi (by norm_num)
  rw [← hsplit]
  exact gammaDeriv_dom_integrableOn_Ioo.union gammaDeriv_dom_integrableOn_Ici

/-- OBLIGATION 2: pointwise domination of the s-derivative of the Gamma
integrand, uniformly for s in (1/2, 3/2). -/
theorem gammaDeriv_dominated (u : ℝ) (hu : 0 < u) (s : ℝ)
    (hs : s ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2)) :
    |Real.exp (-u) * u ^ (s - 1) * Real.log u| ≤ gammaDeriv_dom u := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold gammaDeriv_dom
  have hexp : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  have hrpow : (0:ℝ) < u ^ (s - 1) := Real.rpow_pos_of_pos hu _
  have hkey : u ^ (s - 1) ≤ u ^ (-(1:ℝ)/2) + u ^ ((1:ℝ)/2) := by
    rcases le_total u 1 with hu1 | hu1
    · have hmono : u ^ (s - 1) ≤ u ^ (-(1:ℝ)/2) := by
        apply Real.rpow_le_rpow_of_exponent_ge hu hu1
        linarith
      have hpos : (0:ℝ) < u ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hu _
      linarith
    · have hmono : u ^ (s - 1) ≤ u ^ ((1:ℝ)/2) := by
        apply Real.rpow_le_rpow_of_exponent_le hu1
        linarith
      have hpos : (0:ℝ) < u ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hu _
      linarith
  rw [abs_mul, abs_of_pos (mul_pos hexp hrpow)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left hkey hexp.le

/-- OBLIGATION 3: the pointwise derivative in s of the Gamma integrand. -/
theorem hasDerivAt_gamma_integrand (u : ℝ) (hu : 0 < u) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-u) * u ^ (t - 1))
      (Real.exp (-u) * u ^ (s - 1) * Real.log u) s := by
  have hbase : HasDerivAt (fun t : ℝ => u ^ (t - 1))
      (u ^ (s - 1) * Real.log u) s := by
    have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    have h := hsub.const_rpow hu
    simpa [mul_comm] using h
  have := hbase.const_mul (Real.exp (-u))
  simpa [mul_assoc] using this

/-- The Gamma integral as a function of s, on the region where it converges. -/
noncomputable def gammaInt (s : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (s - 1)

/-- OBLIGATION 4a: differentiation under the integral sign for gammaInt at any
s in (1/2, 3/2), via dominated convergence with gammaDeriv_dom. -/
theorem hasDerivAt_gammaInt (s : ℝ) (hs : s ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2)) :
    HasDerivAt gammaInt
      (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (s - 1) * Real.log u) s := by
  have hsnhds : Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2) ∈ nhds s :=
    Ioo_mem_nhds hs.1 hs.2
  have hmeas : ∀ᶠ x in nhds s,
      MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => Real.exp (-u) * u ^ (x - 1))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    filter_upwards with x
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hint : MeasureTheory.Integrable
      (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have h := Real.GammaIntegral_convergent (s := s) (by linarith [hs.1])
    exact h
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-u) * u ^ (s - 1) * Real.log u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbnd : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∀ x ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2),
        ‖Real.exp (-u) * u ^ (x - 1) * Real.log u‖ ≤ gammaDeriv_dom u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu x hx
    rw [Real.norm_eq_abs]
    exact gammaDeriv_dominated u (Set.mem_Ioi.mp hu) x hx
  have hdif : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∀ x ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2),
        HasDerivAt (fun t : ℝ => Real.exp (-u) * u ^ (t - 1))
          (Real.exp (-u) * u ^ (x - 1) * Real.log u) x := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu x _
    exact hasDerivAt_gamma_integrand u (Set.mem_Ioi.mp hu) x
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hsnhds hmeas hint hmeas' hbnd gammaDeriv_dom_integrable hdif
  exact hmain.2

/-- OBLIGATION 4 (main construction): differentiation under the integral sign
for the real Gamma function on the interval (1/2, 3/2). -/
theorem hasDerivAt_Gamma (s : ℝ) (hs : s ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2)) :
    HasDerivAt Real.Gamma
      (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (s - 1) * Real.log u) s := by
  have hEq : Set.EqOn Real.Gamma gammaInt (Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2)) := by
    intro t ht
    have htpos : (0:ℝ) < t := by
      have := ht.1
      linarith
    rw [Real.Gamma_eq_integral htpos]
    unfold gammaInt
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only
    try ring
  have hnhds : Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2) ∈ nhds s := Ioo_mem_nhds hs.1 hs.2
  have hev : Real.Gamma =ᶠ[nhds s] gammaInt :=
    Filter.eventuallyEq_of_mem hnhds hEq
  exact (hasDerivAt_gammaInt s hs).congr_of_eventuallyEq hev

/-- OBLIGATION 5: Gamma'(1) = -gamma, from the pin's digamma_one. -/
theorem deriv_Gamma_one :
    deriv Real.Gamma 1 = -Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniConstant_eq_neg_deriv
  linarith [h]

/-- TARGET: Euler's integral for gamma. Combine Obligations 4 and 5 at s = 1
(where u ^ (1 - 1) = 1). -/
theorem eulerMascheroni_eq_integral :
    Real.eulerMascheroniConstant
      = -∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * Real.log u := by
  have hmem : (1:ℝ) ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2) := by
    constructor <;> norm_num
  have hd := hasDerivAt_Gamma 1 hmem
  have hsimp : (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ ((1:ℝ) - 1) * Real.log u)
      = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * Real.log u := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : (0:ℝ) < u := Set.mem_Ioi.mp hu
    simp only
    rw [show (1:ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one]
  rw [hsimp] at hd
  have hderiv : deriv Real.Gamma 1
      = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * Real.log u := hd.deriv
  rw [deriv_Gamma_one] at hderiv
  linarith [hderiv]

/-- Ein(a) = int_0^a (1 - e^(-v))/v dv (the entire exponential integral).
The integrand extends continuously by 1 at v = 0. -/
noncomputable def Ein (a : ℝ) : ℝ :=
  ∫ v in Set.Ioc (0:ℝ) a, (1 - Real.exp (-v)) / v

/-- The Ein integrand is bounded by 1 on positives: 0 <= (1-e^(-v))/v <= 1. -/
theorem ein_integrand_bounds (v : ℝ) (hv : 0 < v) :
    0 ≤ (1 - Real.exp (-v)) / v ∧ (1 - Real.exp (-v)) / v ≤ 1 := by
  have h1 : Real.exp (-v) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  have h2 : (1:ℝ) - v ≤ Real.exp (-v) := by
    have := Real.add_one_le_exp (-v)
    linarith
  constructor
  · apply div_nonneg _ hv.le
    linarith
  · rw [div_le_one hv]
    linarith

/-- The Ein integrand is integrable on any (0, a]. -/
theorem ein_integrable (a : ℝ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun v : ℝ => (1 - Real.exp (-v)) / v)
      (Set.Ioc 0 a) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun v : ℝ => (1 - Real.exp (-v)) / v)
      (MeasureTheory.volume.restrict (Set.Ioc 0 a)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbound : MeasureTheory.IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioc 0 a) := by
    have hfin : MeasureTheory.volume (Set.Ioc (0:ℝ) a) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const hfin
  apply MeasureTheory.Integrable.mono hbound hmeas
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
  obtain ⟨hv0, _⟩ := hv
  obtain ⟨hlow, hhigh⟩ := ein_integrand_bounds v hv0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlow, abs_one]
  exact hhigh

/-- The tail integrand e^(-v)/v is integrable on [a, infty) for a > 0,
dominated by e^(-v)/a. -/
theorem exp_div_integrableOn_Ici (a : ℝ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-v) / v) (Set.Ici a) := by
  have hexp : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-v) / a) (Set.Ici a) := by
    have hbase : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ici a) := by
      have h := Real.GammaIntegral_convergent (s := (1:ℝ)) (by norm_num)
      have hsub : Set.Ici a ⊆ Set.Ioi (0:ℝ) := by
        intro x hx
        simp only [Set.mem_Ici] at hx
        simp only [Set.mem_Ioi]
        linarith
      have h2 : MeasureTheory.IntegrableOn
          (fun u : ℝ => Real.exp (-u) * u ^ ((1:ℝ) - 1)) (Set.Ioi 0) := h
      have h3 : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi 0) := by
        apply h2.congr_fun ?_ measurableSet_Ioi
        intro u hu
        simp only
        rw [show (1:ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one]
      exact h3.mono hsub le_rfl
    exact hbase.div_const a
  apply MeasureTheory.Integrable.mono hexp
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with v hv
    have hva : a ≤ v := hv
    have hv0 : (0:ℝ) < v := by linarith
    have hE : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-v) / v),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-v) / a)]
    apply div_le_div_of_nonneg_left hE.le ha hva

/-- CONSEQUENCE (manuscript Thm 4.1, upper bound input): the exact evaluation
int_0^1 (exp(-a t) - 1 + a t)/t^2 dt = a log a + gamma a - a + 1 + a E1(a) - exp(-a).
Only the inequality version is needed downstream; see the manuscript proof of
Theorem 4.1, where a E1(a) <= exp(-a) is used. Stated here for the record. -/
theorem gap_five_evaluation (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioc (0:ℝ) 1, (Real.exp (-a * t) - 1 + a * t) / t ^ 2
      ≤ a * Real.log a + Real.eulerMascheroniConstant * a - a + 1 := by
  sorry

end BanksMartin
