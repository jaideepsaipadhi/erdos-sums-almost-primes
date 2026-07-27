/-- THE s -> 1 LIMIT: g_i(s) -> c_i as s -> 1 from above.
This is the fact deferred since section 2 and needed by section 3.5's mean
value step.  It cannot be stated as g_i(1) = c_i: kappaFac 1 = 0 by the
tprod junk-value convention (cFac diverges at s = 1), so G2manu is not
defined there.  cCoeff is defined instead through G2at1's explicit product. -/
theorem gManu_tendsto_cCoeff (i : ℕ) (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ s : ℝ, s ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu s (circleMap 0 (2:ℝ) theta)) ≤ M0) :
    Filter.Tendsto (fun s : ℝ => gManu i s) (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (cCoeff i)) := by
  have hpi : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hint := contour_integral_tendsto i M0 hM00 hM0
  have hci : ∀ s : ℝ, s ∈ Set.Ioi (1:ℝ) →
      gManu i s = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (∫ theta in Set.Ioc (0:ℝ) (2 * Real.pi),
          deriv (circleMap 0 (2:ℝ)) theta
            * ((1 / circleMap 0 (2:ℝ) theta) ^ i
              * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2manu s (circleMap 0 (2:ℝ) theta)))) := by
    intro s hs
    have hkap : 0 < kappaFac s := kappaFac_pos s hs (cFac_pos s hs)
    rw [gManu_eq_circleIntegral s (le_of_lt hs) hkap i]
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le hpi]
    simp only [smul_eq_mul]
  have hcc : cCoeff i = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
      • (∫ theta in Set.Ioc (0:ℝ) (2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹ * G2at1 (circleMap 0 (2:ℝ) theta)))) := by
    rw [cCoeff_eq_circleIntegral i]
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le hpi]
    simp only [smul_eq_mul]
  rw [hcc]
  apply (hint.const_smul _).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hci s hs).symm
