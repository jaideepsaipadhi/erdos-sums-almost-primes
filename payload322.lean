/-- log^2 p <= (64/9) p^(3/4) for p >= 3.
From log y <= y - 1 at y = p^(3/8): log p = (8/3) log y <= (8/3)(y-1) <= (8/3)y,
so log^2 p <= (64/9) y^2 = (64/9) p^(3/4).
Needed for the r=2 chain, where the per-term derivative carries log^2 p and
log_le_sqrt (exponent 1/2) is too tight -- log^2 p > sqrt p already at p = 5. -/
theorem log_sq_le (x : ℝ) (hx : 3 ≤ x) :
    (Real.log x) ^ 2 ≤ (64/9) * x ^ ((3:ℝ)/4) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hy : (0:ℝ) < x ^ ((3:ℝ)/8) := Real.rpow_pos_of_pos hx0 _
  have hlogy : Real.log (x ^ ((3:ℝ)/8)) ≤ x ^ ((3:ℝ)/8) - 1 :=
    Real.log_le_sub_one_of_pos hy
  have hlogx : Real.log x = (8/3) * Real.log (x ^ ((3:ℝ)/8)) := by
    rw [Real.log_rpow hx0]
    ring
  have hbound : Real.log x ≤ (8/3) * x ^ ((3:ℝ)/8) := by
    rw [hlogx]
    nlinarith [hlogy, hy]
  have hnn : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : x ^ ((3:ℝ)/4) = (x ^ ((3:ℝ)/8)) ^ (2:ℕ) := by
    rw [← Real.rpow_natCast (x ^ ((3:ℝ)/8)) 2, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  rw [hsq]
  nlinarith [hbound, hnn, hy]
