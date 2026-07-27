/-- The correction term is continuous in s on {s // 1 <= s}.
The subtype domain is what makes continuous_tsum applicable: continuity fails
for small s (1 - p^(-s) -> 0 there) and the bound 18 p^(-2) needs s >= 1, so
both hold unconditionally only after restricting. -/
theorem correction_continuous_s (p : ℕ) (hp : 3 ≤ p) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      -Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-(s:ℝ)) : ℝ) : ℂ))
        + z * ((Real.log (1 - (((p:ℕ):ℝ)) ^ (-(s:ℝ))) : ℝ) : ℂ)) := by
  have hp3 : (3:ℝ) ≤ (((p:ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (((p:ℕ):ℝ)) := by linarith
  have hsub : Continuous (fun s : {s : ℝ // 1 ≤ s} => (s:ℝ)) := continuous_subtype_val
  have hrpow : Continuous (fun s : {s : ℝ // 1 ≤ s} => (((p:ℕ):ℝ)) ^ (-(s:ℝ))) :=
    (continuous_const_rpow (ne_of_gt hp0)).comp hsub.neg
  have hlt : ∀ s : {s : ℝ // 1 ≤ s}, (((p:ℕ):ℝ)) ^ (-(s:ℝ)) < 1 :=
    fun s => Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith [s.2])
  have hden : ∀ s : {s : ℝ // 1 ≤ s},
      (0:ℝ) < 1 - (((p:ℕ):ℝ)) ^ (-(s:ℝ)) := fun s => by linarith [hlt s]
  have hlogr : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      Real.log (1 - (((p:ℕ):ℝ)) ^ (-(s:ℝ)))) :=
    Real.continuousOn_log.comp_continuous (continuous_const.sub hrpow)
      (fun s => ne_of_gt (hden s))
  have hinner : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (1 : ℂ) - z * (((((p:ℕ):ℝ)) ^ (-(s:ℝ)) : ℝ) : ℂ)) :=
    continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp hrpow))
  have hslit : ∀ s : {s : ℝ // 1 ≤ s},
      (1 : ℂ) - z * (((((p:ℕ):ℝ)) ^ (-(s:ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    fun s => one_sub_mem_slitPlane p hp (s:ℝ) s.2 z hz
  have hlogc : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      Complex.log (1 - z * (((((p:ℕ):ℝ)) ^ (-(s:ℝ)) : ℝ) : ℂ))) :=
    Complex.continuousOn_log.comp_continuous hinner hslit
  exact hlogc.neg.add (continuous_const.mul (Complex.continuous_ofReal.comp hlogr))
