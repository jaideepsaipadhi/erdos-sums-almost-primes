/-- MANUSCRIPT LEMMA 3.8 at r = 2: the contour integral may be differentiated
twice in s.  Theorem 6.1's Taylor-with-integral-remainder needs exactly this.

M2 bounds the second derivative on the contour, as M bounds the first at r=1:
certified numerically in the manuscript (section 6.1's sup_{s,|z|=2.9}
|G2^(2,0)| <= 19881), so a hypothesis here. -/
theorem lemma_3_8_integral_r2 (i : ℕ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1:ℝ) 2)
    (D2 : ℝ → ℝ → ℂ)
    (hD2cont : ∀ x : ℝ, Continuous (D2 x))
    (hD2 : ∀ x ∈ Set.Ioo (1:ℝ) 2, ∀ theta : ℝ,
      HasDerivAt (fun u : ℝ => deriv (fun v : ℝ => G2manu v (circleMap 0 (2:ℝ) theta)) u)
        (D2 x theta) x)
    (M2 : ℝ) (hM20 : 0 ≤ M2)
    (hM2 : ∀ x ∈ Set.Ioo (1:ℝ) 2, ∀ theta : ℝ,
      Norm.norm (D2 x theta) ≤ M2)
    (hDcont : ∀ x : ℝ, Continuous (fun theta : ℝ =>
      deriv (fun v : ℝ => G2manu v (circleMap 0 (2:ℝ) theta)) x)) :
    HasDerivAt (fun t : ℝ => ∫ theta in (0:ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹
              * deriv (fun v : ℝ => G2manu v (circleMap 0 (2:ℝ) theta)) t)))
      (∫ theta in (0:ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2:ℝ)) theta
          * ((1 / circleMap 0 (2:ℝ) theta) ^ i
            * ((circleMap 0 (2:ℝ) theta)⁻¹ * D2 s theta))) s := by
  have hR : (0:ℝ) < 2 := by norm_num
  have hne : ∀ t : ℝ, circleMap 0 (2:ℝ) t ≠ 0 :=
    fun t => circleMap_ne_center (ne_of_gt hR)
  have hcm : Continuous (circleMap 0 (2:ℝ)) := continuous_circleMap 0 _
  have hdcm : Continuous (deriv (circleMap 0 (2:ℝ))) := by
    have hd : deriv (circleMap 0 (2:ℝ)) = fun t => circleMap 0 (2:ℝ) t * Complex.I := by
      funext t
      exact deriv_circleMap 0 (2:ℝ) t
    rw [hd]
    exact hcm.mul continuous_const
  have hnhds : Set.Ioo (1:ℝ) 2 ∈ nhds s := Ioo_mem_nhds hsmem.1 hsmem.2
  have hsfree : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun theta : ℝ =>
      deriv (circleMap 0 (2:ℝ)) theta
        * ((1 / circleMap 0 (2:ℝ) theta) ^ i
          * ((circleMap 0 (2:ℝ) theta)⁻¹ * g theta))) := by
    intro g hg
    apply hdcm.mul
    apply Continuous.mul
    · exact (continuous_const.div hcm (fun t => hne t)).pow i
    · exact (hcm.inv₀ (fun t => hne t)).mul hg
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℝ) (theta : ℝ) =>
      deriv (circleMap 0 (2:ℝ)) theta
        * ((1 / circleMap 0 (2:ℝ) theta) ^ i
          * ((circleMap 0 (2:ℝ) theta)⁻¹
            * deriv (fun v : ℝ => G2manu v (circleMap 0 (2:ℝ) theta)) x)))
    (F' := fun (x : ℝ) (theta : ℝ) =>
      deriv (circleMap 0 (2:ℝ)) theta
        * ((1 / circleMap 0 (2:ℝ) theta) ^ i
          * ((circleMap 0 (2:ℝ) theta)⁻¹ * D2 x theta)))
    (bound := fun _ => M2) (x₀ := s) (s := Set.Ioo (1:ℝ) 2)
    hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hnhds] with x _
    exact (hsfree _ (hDcont x)).aestronglyMeasurable
  · exact ((hsfree _ (hDcont s)).intervalIntegrable 0 (2 * Real.pi))
  · exact (hsfree _ (hD2cont s)).aestronglyMeasurable
  · filter_upwards with theta _ x hx
    exact contour_integrand_bound_gen i M2 hM20 theta (D2 x theta) (hM2 x hx theta)
  · exact intervalIntegrable_const
  · filter_upwards with theta _ x hx
    exact ((hD2 x hx theta).const_mul _).const_mul _ |>.const_mul _
