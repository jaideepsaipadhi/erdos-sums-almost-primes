/-- Uniform bound for the r=2 per-prime derivative:
|d/ds term| <= 150 log^2 p p^(-2), s-free for s >= 1.
Crude route: |z-1| <= 3, (p^s-z)+(p^s-1) <= 2p^s, (p^s-1)^2 >= (4/9)p^(2s),
(p^s-z)^2 >= (1/9)p^(2s), giving 6/(4/81) = 121.5; 150 leaves margin. -/
theorem deriv2_prime_term_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(z - 1) * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ s)
        * (((((p:ℝ)) ^ s - z) + (((p:ℝ)) ^ s - 1)))
        / ((((p:ℝ)) ^ s - 1) ^ 2 * ((((p:ℝ)) ^ s - z)) ^ 2)|
      ≤ 150 * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ (-(2:ℝ))) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hps : (3:ℝ) ≤ ((p:ℝ)) ^ s := by
    calc (3:ℝ) = (3:ℝ) ^ (1:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p:ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0:ℝ) < ((p:ℝ)) ^ s := by linarith
  have hzabs := abs_le.mp hz
  have hlog0 : (0:ℝ) ≤ (Real.log (p:ℝ)) ^ 2 := sq_nonneg _
  have hnum : |(z - 1) * (Real.log (p:ℝ)) ^ 2 * (((p:ℝ)) ^ s)
        * (((((p:ℝ)) ^ s - z) + (((p:ℝ)) ^ s - 1)))|
      ≤ 6 * (Real.log (p:ℝ)) ^ 2 * ((((p:ℝ)) ^ s)) ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hlog0, abs_of_pos hps0]
    have h1 : |z - 1| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hzabs.1, hzabs.2]
    have h2 : |(((p:ℝ)) ^ s - z) + (((p:ℝ)) ^ s - 1)| ≤ 2 * ((p:ℝ)) ^ s := by
      rw [abs_le]; constructor <;> linarith [hzabs.1, hzabs.2]
    nlinarith [h1, h2, hlog0, hps0, abs_nonneg (z - 1),
      abs_nonneg ((((p:ℝ)) ^ s - z) + (((p:ℝ)) ^ s - 1))]
  have hd1 : (2/3) * ((p:ℝ)) ^ s ≤ ((p:ℝ)) ^ s - 1 := by linarith
  have hd2 : (1/3) * ((p:ℝ)) ^ s ≤ ((p:ℝ)) ^ s - z := by linarith [hzabs.2]
  have hden : (4/81) * ((((p:ℝ)) ^ s)) ^ 4
      ≤ (((p:ℝ)) ^ s - 1) ^ 2 * ((((p:ℝ)) ^ s - z)) ^ 2 := by
    nlinarith [hd1, hd2, hps0]
  have hdenpos : (0:ℝ) < (((p:ℝ)) ^ s - 1) ^ 2 * ((((p:ℝ)) ^ s - z)) ^ 2 := by
    nlinarith [hd1, hd2, hps0]
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  have hpow : ((p:ℝ)) ^ (-(2:ℝ)) * ((((p:ℝ)) ^ s)) ^ 2 ≥ 1 := by
    have hsq : ((((p:ℝ)) ^ s)) ^ 2 = ((p:ℝ)) ^ (2*s) := by
      rw [← Real.rpow_natCast (((p:ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
      norm_num
      ring_nf
    rw [hsq, ← Real.rpow_add hp0]
    calc (1:ℝ) = ((p:ℝ)) ^ (0:ℝ) := by rw [Real.rpow_zero]
      _ ≤ ((p:ℝ)) ^ (-(2:ℝ) + 2*s) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  nlinarith [hnum, hden, hpow, hlog0, hps0, hdenpos]
