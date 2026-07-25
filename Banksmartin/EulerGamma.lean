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

/-- OBLIGATION 1: the dominating function is integrable on (0, infty). -/
theorem gammaDeriv_dom_integrable :
    IntegrableOn gammaDeriv_dom (Set.Ioi 0) := by
  sorry

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

/-- OBLIGATION 4 (main construction): differentiation under the integral sign
for the real Gamma function on the interval (1/2, 3/2). -/
theorem hasDerivAt_Gamma (s : ℝ) (hs : s ∈ Set.Ioo ((1:ℝ)/2) ((3:ℝ)/2)) :
    HasDerivAt Real.Gamma
      (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (s - 1) * Real.log u) s := by
  sorry

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
