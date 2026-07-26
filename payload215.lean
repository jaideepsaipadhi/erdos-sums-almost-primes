/-- The cCoeff are exactly the Cauchy power series coefficients of G2at1. -/
theorem cCoeff_eq_coeff (n : ℕ) :
    cCoeff n = (cauchyPowerSeries G2at1 0 (3/2 : ℝ≥0)).coeff n := by
  have hser := G2at1_differentiableOn.hasFPowerSeriesOnBall (R := (3/2 : ℝ≥0)) (by norm_num)
  have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser n
  unfold cCoeff
  rw [hbridge]
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- MANUSCRIPT section 1: sum_i c_i = 1/2.
The series converges at z = 1 (radius 3/2 > 1), and G2at1 1 = (1/2) G2C(1,1) = 1/2. -/
theorem cCoeff_sum : HasSum (fun n : ℕ => cCoeff n) (1/2 : ℂ) := by
  have hser := G2at1_differentiableOn.hasFPowerSeriesOnBall (R := (3/2 : ℝ≥0)) (by norm_num)
  have hmem : (1 : ℂ) ∈ EMetric.ball (0 : ℂ) ((3/2 : ℝ≥0) : ENNReal) := by
    rw [EMetric.mem_ball, edist_zero_right]
    simp only [enorm_one]
    norm_num
  have hsum := hser.hasSum_sub hmem
  simp only [sub_zero] at hsum
  have hval : G2at1 1 = (1/2 : ℂ) := by
    unfold G2at1
    rw [G2C_one_one, mul_one, Complex.cpow_one]
    norm_num
  rw [hval] at hsum
  apply hsum.congr_fun
  intro n
  rw [cCoeff_eq_coeff]
  rfl
