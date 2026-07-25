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

/-- Ein as an interval integral, matching Mathlib's FTC shape. -/
theorem Ein_eq_intervalIntegral (a : ℝ) (ha : 0 ≤ a) :
    Ein a = ∫ v in (0:ℝ)..a, (1 - Real.exp (-v)) / v := by
  unfold Ein
  rw [intervalIntegral.integral_of_le ha]

/-- The Ein integrand is interval-integrable on any [0, b] with b > 0. -/
theorem ein_intervalIntegrable (b : ℝ) (hb : 0 < b) :
    IntervalIntegrable (fun v : ℝ => (1 - Real.exp (-v)) / v) MeasureTheory.volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  exact ein_integrable b hb

theorem hasDerivAt_Ein (a : ℝ) (ha : 0 < a) :
    HasDerivAt Ein ((1 - Real.exp (-a)) / a) a := by
  have hcont : ContinuousAt (fun v : ℝ => (1 - Real.exp (-v)) / v) a := by
    apply ContinuousAt.div
    · exact continuousAt_const.sub (Real.continuous_exp.comp continuous_neg).continuousAt
    · exact continuousAt_id
    · exact ne_of_gt ha
  have hmeas : StronglyMeasurableAtFilter
      (fun v : ℝ => (1 - Real.exp (-v)) / v) (nhds a) := by
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hint := ein_intervalIntegrable a ha
  have hFTC := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hEq : Ein =ᶠ[nhds a] fun t : ℝ => ∫ v in (0:ℝ)..t, (1 - Real.exp (-v)) / v := by
    filter_upwards [Ioi_mem_nhds ha] with t ht
    exact Ein_eq_intervalIntegral t (le_of_lt ht)
  exact hFTC.congr_of_eventuallyEq hEq

/-- The tail function T(a) = int_{[a,inf)} e^(-v)/v has derivative -e^(-a)/a. -/
noncomputable def EinTailFun (a : ℝ) : ℝ :=
  ∫ v in Set.Ici a, Real.exp (-v) / v

/-- The tail function splits at any reference point: T(a) = T(1) - int_1^a e^-v/v. -/
theorem EinTailFun_split (a : ℝ) (ha : 0 < a) :
    EinTailFun a = EinTailFun 1 - ∫ v in (1:ℝ)..a, Real.exp (-v) / v := by
  unfold EinTailFun
  rcases le_total (1:ℝ) a with h1 | h1
  · have hunion : Set.Ici (1:ℝ) = Set.Ico 1 a ∪ Set.Ici a :=
      (Set.Ico_union_Ici_eq_Ici h1).symm
    have hdisj : Disjoint (Set.Ico (1:ℝ) a) (Set.Ici a) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact absurd (Set.mem_Ici.mp hx2) (not_le.mpr hx.2)
    have hint1 : MeasureTheory.IntegrableOn
        (fun v : ℝ => Real.exp (-v) / v) (Set.Ico 1 a) :=
      (exp_div_integrableOn_Ici 1 (by norm_num)).mono
        (fun x hx => Set.mem_Ici.mpr hx.1) le_rfl
    have hint2 : MeasureTheory.IntegrableOn
        (fun v : ℝ => Real.exp (-v) / v) (Set.Ici a) :=
      exp_div_integrableOn_Ici a ha
    have hadd : (∫ v in Set.Ici (1:ℝ), Real.exp (-v) / v)
        = (∫ v in Set.Ico (1:ℝ) a, Real.exp (-v) / v)
          + ∫ v in Set.Ici a, Real.exp (-v) / v := by
      rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ici hint1 hint2]
    have hIcoIoc : (∫ v in Set.Ico (1:ℝ) a, Real.exp (-v) / v)
        = ∫ v in Set.Ioc (1:ℝ) a, Real.exp (-v) / v := by
      rw [MeasureTheory.integral_Ico_eq_integral_Ioo,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [intervalIntegral.integral_of_le h1, ← hIcoIoc]
    linarith [hadd]
  · have hunion : Set.Ici a = Set.Ico a 1 ∪ Set.Ici 1 :=
      (Set.Ico_union_Ici_eq_Ici h1).symm
    have hdisj : Disjoint (Set.Ico a (1:ℝ)) (Set.Ici 1) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact absurd (Set.mem_Ici.mp hx2) (not_le.mpr hx.2)
    have hint1 : MeasureTheory.IntegrableOn
        (fun v : ℝ => Real.exp (-v) / v) (Set.Ico a 1) :=
      (exp_div_integrableOn_Ici a ha).mono
        (fun x hx => Set.mem_Ici.mpr hx.1) le_rfl
    have hint2 : MeasureTheory.IntegrableOn
        (fun v : ℝ => Real.exp (-v) / v) (Set.Ici 1) :=
      exp_div_integrableOn_Ici 1 (by norm_num)
    have hadd : (∫ v in Set.Ici a, Real.exp (-v) / v)
        = (∫ v in Set.Ico a (1:ℝ), Real.exp (-v) / v)
          + ∫ v in Set.Ici 1, Real.exp (-v) / v := by
      rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ici hint1 hint2]
    have hIcoIoc : (∫ v in Set.Ico a (1:ℝ), Real.exp (-v) / v)
        = ∫ v in Set.Ioc a (1:ℝ), Real.exp (-v) / v := by
      rw [MeasureTheory.integral_Ico_eq_integral_Ioo,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [intervalIntegral.integral_of_ge h1, ← hIcoIoc]
    linarith [hadd]

/-- The antiderivative identity behind integration by parts for the Euler
integrand: d/dv [-e^(-v) log v] = e^(-v) log v - e^(-v)/v, for v > 0. -/
theorem hasDerivAt_negExpLog (v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun t : ℝ => -(Real.exp (-t) * Real.log t))
      (Real.exp (-v) * Real.log v - Real.exp (-v) / v) v := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-(Real.exp (-v))) v := by
    have h : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-v) * -1) v :=
      (Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)
    simpa using h
  have hlog : HasDerivAt Real.log v⁻¹ v := Real.hasDerivAt_log (ne_of_gt hv)
  have hmul := hexp.mul hlog
  have hneg := hmul.neg
  have harith : -(-(Real.exp (-v)) * Real.log v + Real.exp (-v) * v⁻¹)
      = Real.exp (-v) * Real.log v - Real.exp (-v) / v := by
    field_simp
    try ring
  rw [harith] at hneg
  exact hneg

/-- Finite-interval integration by parts for the Euler integrand. -/
theorem euler_parts_core (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    (∫ v in b..c, (Real.exp (-v) * Real.log v - Real.exp (-v) / v))
      = -(Real.exp (-c) * Real.log c) + Real.exp (-b) * Real.log b := by
  have hderiv : ∀ x ∈ Set.uIcc b c,
      HasDerivAt (fun t : ℝ => -(Real.exp (-t) * Real.log t))
        (Real.exp (-x) * Real.log x - Real.exp (-x) / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hbc] at hx
    exact hasDerivAt_negExpLog x (by linarith [hx.1])
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.exp (-v) * Real.log v - Real.exp (-v) / v)
      MeasureTheory.volume b c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbc]
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · exact (Real.continuous_exp.comp continuous_neg).continuousOn
      · apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [id_eq]
        exact ne_of_gt (by linarith [hx.1])
    · apply ContinuousOn.div
      · exact (Real.continuous_exp.comp continuous_neg).continuousOn
      · exact continuousOn_id
      · intro x hx
        exact ne_of_gt (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The regularized antiderivative: d/dv [(1 - e^(-v)) log v]
= e^(-v) log v - (e^(-v) - 1)/v, for v > 0. Unlike the raw by-parts form,
the boundary term (1 - e^(-b)) log b tends to 0 as b -> 0+. -/
theorem hasDerivAt_regAntideriv (v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t)
      (Real.exp (-v) * Real.log v - (Real.exp (-v) - 1) / v) v := by
  have hexp : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-v)) v := by
    have h : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-v) * -1) v :=
      (Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-(Real.exp (-v))) v := by
      simpa using h
    simpa using h2.const_sub 1
  have hlog : HasDerivAt Real.log v⁻¹ v := Real.hasDerivAt_log (ne_of_gt hv)
  have hmul := hexp.mul hlog
  have harith : Real.exp (-v) * Real.log v + (1 - Real.exp (-v)) * v⁻¹
      = Real.exp (-v) * Real.log v - (Real.exp (-v) - 1) / v := by
    field_simp
    try ring
  rw [harith] at hmul
  exact hmul

/-- Regularized integration by parts on [b, c], 0 < b <= c. -/
theorem euler_parts_reg (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    (∫ v in b..c, (Real.exp (-v) * Real.log v - (Real.exp (-v) - 1) / v))
      = (1 - Real.exp (-c)) * Real.log c - (1 - Real.exp (-b)) * Real.log b := by
  have hderiv : ∀ x ∈ Set.uIcc b c,
      HasDerivAt (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t)
        (Real.exp (-x) * Real.log x - (Real.exp (-x) - 1) / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hbc] at hx
    exact hasDerivAt_regAntideriv x (by linarith [hx.1])
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.exp (-v) * Real.log v - (Real.exp (-v) - 1) / v)
      MeasureTheory.volume b c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbc]
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · exact (Real.continuous_exp.comp continuous_neg).continuousOn
      · apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [id_eq]
        exact ne_of_gt (by linarith [hx.1])
    · apply ContinuousOn.div
      · exact ((Real.continuous_exp.comp continuous_neg).sub continuous_const).continuousOn
      · exact continuousOn_id
      · intro x hx
        exact ne_of_gt (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- The regularized boundary term vanishes at 0: (1 - e^(-b)) log b -> 0. -/
theorem regBoundary_tendsto_zero :
    Filter.Tendsto (fun b : ℝ => (1 - Real.exp (-b)) * Real.log b)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hxlogx : Filter.Tendsto (fun b : ℝ => b * Real.log b)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := (1:ℝ)) zero_lt_one
    simp only [Real.rpow_one] at h
    simpa [mul_comm] using h
  have habs : Filter.Tendsto (fun b : ℝ => |b * Real.log b|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hxlogx.abs
  apply squeeze_zero_norm' _ habs
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb0 : (0:ℝ) < b := hb
  have h1 : 1 - Real.exp (-b) ≤ b := by
    have := Real.add_one_le_exp (-b)
    linarith
  have h2 : (0:ℝ) ≤ 1 - Real.exp (-b) := by
    have hle : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
  rw [abs_mul, abs_of_nonneg hb0.le]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- Ein tends to 0 at 0+ (the integral over a shrinking interval). -/
theorem Ein_tendsto_zero :
    Filter.Tendsto Ein (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hid : Filter.Tendsto (fun b : ℝ => b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hid
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb0 : (0:ℝ) < b := hb
  unfold Ein
  have hle : |∫ v in Set.Ioc (0:ℝ) b, (1 - Real.exp (-v)) / v|
      ≤ ∫ v in Set.Ioc (0:ℝ) b, (1:ℝ) := by
    apply MeasureTheory.abs_integral_le_integral_abs.trans
    apply MeasureTheory.setIntegral_mono_on
    · exact (ein_integrable b hb0).abs
    · have hfin : MeasureTheory.volume (Set.Ioc (0:ℝ) b) ≠ ⊤ := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      exact integrableOn_const hfin
    · exact measurableSet_Ioc
    · intro v hv
      obtain ⟨hlow, hhigh⟩ := ein_integrand_bounds v hv.1
      rw [abs_of_nonneg hlow]
      exact hhigh
  have hconst : (∫ v in Set.Ioc (0:ℝ) b, (1:ℝ)) = b := by
    rw [MeasureTheory.setIntegral_const]
    have hvol : MeasureTheory.volume.real (Set.Ioc (0:ℝ) b) = b := by
      rw [MeasureTheory.measureReal_def, Real.volume_Ioc]
      simp [ENNReal.toReal_ofReal hb0.le]
    rw [hvol]
    ring
  rw [hconst] at hle
  exact hle

/-- Ein additivity: Ein c - Ein b = int_b^c (1 - e^-v)/v, for 0 < b <= c. -/
theorem Ein_sub (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    Ein c - Ein b = ∫ v in Set.Ioc b c, (1 - Real.exp (-v)) / v := by
  unfold Ein
  have hunion : Set.Ioc (0:ℝ) c = Set.Ioc 0 b ∪ Set.Ioc b c :=
    (Set.Ioc_union_Ioc_eq_Ioc hb.le hbc).symm
  have hdisj : Disjoint (Set.Ioc (0:ℝ) b) (Set.Ioc b c) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx2.1 (not_lt.mpr hx.2)
  have hint1 : MeasureTheory.IntegrableOn
      (fun v : ℝ => (1 - Real.exp (-v)) / v) (Set.Ioc 0 b) := ein_integrable b hb
  have hint2 : MeasureTheory.IntegrableOn
      (fun v : ℝ => (1 - Real.exp (-v)) / v) (Set.Ioc b c) :=
    (ein_integrable c (by linarith)).mono
      (fun x hx => Set.mem_Ioc.mpr ⟨by linarith [hx.1], hx.2⟩) le_rfl
  rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2]
  ring

/-- e^(-v) log v is integrable on (0, c] for c > 0, dominated by the
gammaDeriv_dom envelope. -/
theorem expLog_integrableOn_Ioc (c : ℝ) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-v) * Real.log v)
      (Set.Ioc 0 c) := by
  have hdom : MeasureTheory.IntegrableOn gammaDeriv_dom (Set.Ioc 0 c) :=
    gammaDeriv_dom_integrable.mono
      (fun x hx => Set.mem_Ioi.mpr hx.1) le_rfl
  apply MeasureTheory.Integrable.mono hdom
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv
    have hv0 : (0:ℝ) < v := hv.1
    unfold gammaDeriv_dom
    have hA : (0:ℝ) < v ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hv0 _
    have hB : (0:ℝ) < v ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hv0 _
    have hE : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
    have hone : (1:ℝ) ≤ v ^ (-(1:ℝ)/2) + v ^ ((1:ℝ)/2) := by
      rcases le_total v 1 with hv1 | hv1
      · have hstep : v ^ (0:ℝ) ≤ v ^ (-(1:ℝ)/2) := by
          apply Real.rpow_le_rpow_of_exponent_ge hv0 hv1
          norm_num
        rw [Real.rpow_zero] at hstep
        linarith
      · have : (1:ℝ) ≤ v ^ ((1:ℝ)/2) := by
          apply Real.one_le_rpow hv1
          norm_num
        linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hE]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤
      Real.exp (-v) * (v ^ (-(1:ℝ)/2) + v ^ ((1:ℝ)/2)) * |Real.log v|)]
    calc Real.exp (-v) * |Real.log v|
        = Real.exp (-v) * 1 * |Real.log v| := by ring
      _ ≤ Real.exp (-v) * (v ^ (-(1:ℝ)/2) + v ^ ((1:ℝ)/2)) * |Real.log v| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hone hE.le

/-- The b -> 0+ limit of the regularized identity: for c > 0,
int_0^c e^-v log v dv + Ein c = (1 - e^-c) log c. -/
theorem euler_parts_limit (c : ℝ) (hc : 0 < c) :
    (∫ v in Set.Ioc (0:ℝ) c, Real.exp (-v) * Real.log v) + Ein c
      = (1 - Real.exp (-c)) * Real.log c := by
  have hfin : ∀ b ∈ Set.Ioc (0:ℝ) c,
      (∫ v in Set.Ioc (0:ℝ) c, Real.exp (-v) * Real.log v) + Ein c
        = (1 - Real.exp (-c)) * Real.log c - (1 - Real.exp (-b)) * Real.log b
          + ((∫ v in Set.Ioc (0:ℝ) b, Real.exp (-v) * Real.log v) + Ein b) := by
    intro b hb
    have hb0 : (0:ℝ) < b := hb.1
    have hbc : b ≤ c := hb.2
    have hreg := euler_parts_reg b c hb0 hbc
    have hsplit : (∫ v in Set.Ioc (0:ℝ) c, Real.exp (-v) * Real.log v)
        = (∫ v in Set.Ioc (0:ℝ) b, Real.exp (-v) * Real.log v)
          + ∫ v in Set.Ioc b c, Real.exp (-v) * Real.log v := by
      have hunion : Set.Ioc (0:ℝ) c = Set.Ioc 0 b ∪ Set.Ioc b c :=
        (Set.Ioc_union_Ioc_eq_Ioc hb0.le hbc).symm
      have hdisj : Disjoint (Set.Ioc (0:ℝ) b) (Set.Ioc b c) := by
        rw [Set.disjoint_left]
        intro x hx hx2
        exact absurd hx2.1 (not_lt.mpr hx.2)
      have hi1 := expLog_integrableOn_Ioc b hb0
      have hi2 : MeasureTheory.IntegrableOn
          (fun v : ℝ => Real.exp (-v) * Real.log v) (Set.Ioc b c) :=
        (expLog_integrableOn_Ioc c hc).mono
          (fun x hx => Set.mem_Ioc.mpr ⟨by linarith [hx.1], hx.2⟩) le_rfl
      rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hi1 hi2]
    have hinterval : (∫ v in b..c,
        (Real.exp (-v) * Real.log v - (Real.exp (-v) - 1) / v))
        = (∫ v in Set.Ioc b c, Real.exp (-v) * Real.log v)
          + ∫ v in Set.Ioc b c, (1 - Real.exp (-v)) / v := by
      rw [intervalIntegral.integral_of_le hbc]
      have hi2 : MeasureTheory.IntegrableOn
          (fun v : ℝ => Real.exp (-v) * Real.log v) (Set.Ioc b c) :=
        (expLog_integrableOn_Ioc c hc).mono
          (fun x hx => Set.mem_Ioc.mpr ⟨by linarith [hx.1], hx.2⟩) le_rfl
      have hi3 : MeasureTheory.IntegrableOn
          (fun v : ℝ => (1 - Real.exp (-v)) / v) (Set.Ioc b c) :=
        (ein_integrable c hc).mono
          (fun x hx => Set.mem_Ioc.mpr ⟨by linarith [hx.1], hx.2⟩) le_rfl
      rw [← MeasureTheory.integral_add hi2 hi3]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      have hv0 : (0:ℝ) < v := by linarith [hv.1]
      field_simp
      ring
    rw [hinterval, ← Ein_sub b c hb0 hbc] at hreg
    rw [hsplit]
    linarith [hreg]
  have hlim : Filter.Tendsto
      (fun b : ℝ => (1 - Real.exp (-c)) * Real.log c - (1 - Real.exp (-b)) * Real.log b
        + ((∫ v in Set.Ioc (0:ℝ) b, Real.exp (-v) * Real.log v) + Ein b))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 - Real.exp (-c)) * Real.log c)) := by
    have h1 := regBoundary_tendsto_zero
    have h2 := Ein_tendsto_zero
    have h3 : Filter.Tendsto
        (fun b : ℝ => ∫ v in Set.Ioc (0:ℝ) b, Real.exp (-v) * Real.log v)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hmaj : Filter.Tendsto (fun b : ℝ => (16/3) * b ^ ((3:ℝ)/4))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hrpow : Filter.Tendsto (fun b : ℝ => b ^ ((3:ℝ)/4))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          have hcont := Real.continuousAt_rpow_const (0:ℝ) ((3:ℝ)/4) (by norm_num)
          have h0 : (0:ℝ) ^ ((3:ℝ)/4) = 0 := Real.zero_rpow (by norm_num)
          have ht := hcont.continuousWithinAt (s := Set.Ioi (0:ℝ))
          rw [ContinuousWithinAt, h0] at ht
          exact ht
        simpa using hrpow.const_mul ((16:ℝ)/3)
      have hsmall : ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0), b ≤ 1 := by
        have hIio : Set.Iio (1:ℝ) ∈ nhds (0:ℝ) := Iio_mem_nhds (by norm_num)
        filter_upwards [nhdsWithin_le_nhds hIio] with b hb
        exact le_of_lt hb
      apply squeeze_zero_norm' _ hmaj
      filter_upwards [self_mem_nhdsWithin, hsmall] with b hb hb1
      have hb0 : (0:ℝ) < b := hb
      have hbound : |∫ v in Set.Ioc (0:ℝ) b, Real.exp (-v) * Real.log v|
          ≤ ∫ v in Set.Ioc (0:ℝ) b, 4 * v ^ (-(1:ℝ)/4) := by
        apply MeasureTheory.abs_integral_le_integral_abs.trans
        apply MeasureTheory.setIntegral_mono_on
        · exact (expLog_integrableOn_Ioc b hb0).abs
        · have hb2 : MeasureTheory.IntegrableOn
              (fun v : ℝ => v ^ (-(1:ℝ)/4)) (Set.Ioc 0 b) := by
            have hIoo : MeasureTheory.IntegrableOn
                (fun v : ℝ => v ^ (-(1:ℝ)/4)) (Set.Ioo 0 b) := by
              rw [intervalIntegral.integrableOn_Ioo_rpow_iff hb0]
              norm_num
            exact hIoo.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc).symm
          exact hb2.const_mul 4
        · exact measurableSet_Ioc
        · intro v hv
          have hv0 : (0:ℝ) < v := hv.1
          have hv1 : v ≤ 1 := le_trans hv.2 hb1
          have hE : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hEp : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
          have hL := abs_log_le_rpow_near_zero v hv0 hv1
          rw [abs_mul, abs_of_pos hEp]
          calc Real.exp (-v) * |Real.log v| ≤ 1 * (4 * v ^ (-(1:ℝ)/4)) :=
                mul_le_mul hE hL (abs_nonneg _) (by norm_num)
            _ = 4 * v ^ (-(1:ℝ)/4) := by ring
      have hcalc : (∫ v in Set.Ioc (0:ℝ) b, 4 * v ^ (-(1:ℝ)/4))
          = (16/3) * b ^ ((3:ℝ)/4) := by
        have hIoc : (∫ v in Set.Ioc (0:ℝ) b, 4 * v ^ (-(1:ℝ)/4))
            = ∫ v in (0:ℝ)..b, 4 * v ^ (-(1:ℝ)/4) := by
          rw [intervalIntegral.integral_of_le hb0.le]
        rw [hIoc, intervalIntegral.integral_const_mul]
        rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1:ℝ)/4))]
        rw [Real.zero_rpow (by norm_num)]
        have hexp : -(1:ℝ)/4 + 1 = (3:ℝ)/4 := by norm_num
        rw [hexp]
        ring
      rw [hcalc] at hbound
      rw [Real.norm_eq_abs]
      exact hbound
    have hc0 : Filter.Tendsto (fun _ : ℝ => (1 - Real.exp (-c)) * Real.log c)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 - Real.exp (-c)) * Real.log c)) :=
      tendsto_const_nhds
    have hsum := (hc0.sub h1).add (h3.add h2)
    simpa using hsum
  have heq : (fun b : ℝ => (1 - Real.exp (-c)) * Real.log c - (1 - Real.exp (-b)) * Real.log b
      + ((∫ v in Set.Ioc (0:ℝ) b, Real.exp (-v) * Real.log v) + Ein b))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun _ => (∫ v in Set.Ioc (0:ℝ) c, Real.exp (-v) * Real.log v) + Ein c := by
    have hev : ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0), b < c := by
      have hIio : Set.Iio c ∈ nhds (0:ℝ) := Iio_mem_nhds hc
      filter_upwards [nhdsWithin_le_nhds hIio] with b hb
      exact hb
    filter_upwards [self_mem_nhdsWithin, hev] with b hb1 hb2
    exact (hfin b (Set.mem_Ioc.mpr ⟨hb1, le_of_lt hb2⟩)).symm
  have hconst := hlim.congr' heq
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- The truncated Euler integral converges to the full one as c -> infinity. -/
theorem expLog_partial_tendsto :
    Filter.Tendsto (fun n : ℕ => ∫ v in Set.Ioc (0:ℝ) (n:ℝ), Real.exp (-v) * Real.log v)
      Filter.atTop (nhds (∫ v in Set.Ioi (0:ℝ), Real.exp (-v) * Real.log v)) := by
  have hint : MeasureTheory.IntegrableOn
      (fun v : ℝ => Real.exp (-v) * Real.log v) (Set.Ioi 0) := by
    apply MeasureTheory.Integrable.mono gammaDeriv_dom_integrable
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : (0:ℝ) < v := hv
      unfold gammaDeriv_dom
      have hA : (0:ℝ) < v ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hv0 _
      have hB : (0:ℝ) < v ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hv0 _
      have hE : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
      have hone : (1:ℝ) ≤ v ^ (-(1:ℝ)/2) + v ^ ((1:ℝ)/2) := by
        rcases le_total v 1 with hv1 | hv1
        · have hstep : v ^ (0:ℝ) ≤ v ^ (-(1:ℝ)/2) := by
            apply Real.rpow_le_rpow_of_exponent_ge hv0 hv1
            norm_num
          rw [Real.rpow_zero] at hstep
          linarith
        · have hstep : v ^ (0:ℝ) ≤ v ^ ((1:ℝ)/2) := by
            apply Real.rpow_le_rpow_of_exponent_le hv1
            norm_num
          rw [Real.rpow_zero] at hstep
          linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hE]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤
        Real.exp (-v) * (v ^ (-(1:ℝ)/2) + v ^ ((1:ℝ)/2)) * |Real.log v|)]
      calc Real.exp (-v) * |Real.log v| = Real.exp (-v) * 1 * |Real.log v| := by ring
        _ ≤ Real.exp (-v) * (v ^ (-(1:ℝ)/2) + v ^ ((1:ℝ)/2)) * |Real.log v| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hone hE.le
  have hunion : (⋃ n : ℕ, Set.Ioc (0:ℝ) (n:ℝ)) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn, _⟩
      exact hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hx, hn⟩
  have hmono : Monotone (fun n : ℕ => Set.Ioc (0:ℝ) (n:ℝ)) := by
    intro m n hmn
    exact Set.Ioc_subset_Ioc_right (by exact_mod_cast hmn)
  have hnat := MeasureTheory.tendsto_setIntegral_of_monotone
    (fun n : ℕ => measurableSet_Ioc) hmono (by rw [hunion]; exact hint)
  rw [hunion] at hnat
  exact hnat

/-- e^(-n) log n -> 0 along the naturals. -/
theorem expNeg_log_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)) * Real.log (n:ℝ))
      Filter.atTop (nhds 0) := by
  have hmaj : Filter.Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)) * (n:ℝ))
      Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have heq : (fun x : ℝ => x ^ 1 * Real.exp (-x))
        = fun x : ℝ => Real.exp (-x) * x := by
      funext x
      rw [pow_one]
      ring
    rw [heq] at h
    exact h.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' _ hmaj
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hE : (0:ℝ) < Real.exp (-(n:ℝ)) := Real.exp_pos _
  have hL : |Real.log (n:ℝ)| ≤ (n:ℝ) := abs_log_le_self (n:ℝ) hn1
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
  exact mul_le_mul_of_nonneg_left hL hE.le

/-- The exponential tail integral evaluates: int_{Ioi a} e^(-v) dv = e^(-a). -/
theorem integral_Ioi_exp_neg (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Set.Ioi a, Real.exp (-v)) = Real.exp (-a) := by
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-x)) x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-(Real.exp (-x))) x := by
      simpa using h
    have h3 := h2.neg
    simpa [Pi.neg_def] using h3
  have hint : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ioi a) := by
    have hG : MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ ((1:ℝ) - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (s := (1:ℝ)) (by norm_num)
    have hbase : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi 0) := by
      apply hG.congr_fun ?_ measurableSet_Ioi
      intro u _
      simp only
      rw [show (1:ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one]
    exact hbase.mono (fun x hx => Set.mem_Ioi.mpr (lt_of_le_of_lt ha hx)) le_rfl
  have htend : Filter.Tendsto (fun t : ℝ => -Real.exp (-t)) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using h.neg
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain]
  ring

/-- The tail integral vanishes at infinity. -/
theorem EinTailFun_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => EinTailFun (n:ℝ)) Filter.atTop (nhds 0) := by
  sorry

/-- STEP C: Ein(a) = gamma + log a + tail(a). The constant in einCombo_const,
identified via Euler's integral. -/
theorem ein_eq (a : ℝ) (ha : 0 < a) :
    Ein a = Real.eulerMascheroniConstant + Real.log a + EinTailFun a := by
  sorry

/-- CONSEQUENCE (manuscript Thm 4.1, upper bound input): the exact evaluation
int_0^1 (exp(-a t) - 1 + a t)/t^2 dt = a log a + gamma a - a + 1 + a E1(a) - exp(-a).
Only the inequality version is needed downstream; see the manuscript proof of
Theorem 4.1, where a E1(a) <= exp(-a) is used. Stated here for the record. -/
theorem gap_five_evaluation (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioc (0:ℝ) 1, (Real.exp (-a * t) - 1 + a * t) / t ^ 2
      ≤ a * Real.log a + Real.eulerMascheroniConstant * a - a + 1 := by
  sorry

end BanksMartin
