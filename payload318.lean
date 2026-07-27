/-- Pointwise bound for (10)'s integrand on (1,2).
|(g_i(s) - c_i) 2^(-js) L_l(s)| <= beta * 2^(-j) * (L_l(s) * (s-1)),
from the mean value step, 2^(-js) <= 2^(-j) for s >= 1, and L_l >= 0. -/
theorem Dk_integrand_ptwise (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ x ∈ Set.Ioo (1:ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1:ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2:ℝ) theta)) ≤ M0)
    (s : ℝ) (hs : s ∈ Set.Ioo (1:ℝ) 2) :
    |((gManu i s).re - (cCoeff i).re) * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))|
      ≤ beta * (2:ℝ) ^ (-(j:ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
  have hmv := gManu_sub_cCoeff_bound i beta hbeta0 hderiv hbnd M0 hM00 hM0 s hs
  have hL : (0:ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
  have hB : (0:ℝ) < (2:ℝ) ^ (-(j:ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  have hBle : (2:ℝ) ^ (-(j:ℝ) * s) ≤ (2:ℝ) ^ (-(j:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hj : (0:ℝ) ≤ (j:ℝ) := by positivity
    nlinarith [hs.1]
  have hA : |(gManu i s).re - (cCoeff i).re| ≤ beta * (s - 1) := by
    have hre : |(gManu i s).re - (cCoeff i).re|
        = |(gManu i s - cCoeff i).re| := by
      rw [Complex.sub_re]
    rw [hre]
    exact le_trans (Complex.abs_re_le_norm _) hmv
  have hs1 : (0:ℝ) ≤ s - 1 := by linarith [hs.1]
  rw [abs_mul, abs_mul, abs_of_pos hB, abs_of_nonneg hL]
  calc |(gManu i s).re - (cCoeff i).re| * (2:ℝ) ^ (-(j:ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))
      ≤ (beta * (s - 1)) * (2:ℝ) ^ (-(j:ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)) := by
        apply mul_le_mul_of_nonneg_right _ hL
        apply mul_le_mul hA hBle (le_of_lt hB) (by positivity)
    _ = beta * (2:ℝ) ^ (-(j:ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by ring
