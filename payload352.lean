/-- The series that makes Theorem 6.1's Gamma k-independent:
sum_{l>=0} 2^l 3^(-l-1) = 1 exactly.
This is why the l-sum in the remainder bound does not grow with k. -/
theorem geom_two_three : HasSum (fun l : ℕ => (2:ℝ) ^ l * (1 / (3:ℝ) ^ (l + 1))) 1 := by
  have hgeom : HasSum (fun l : ℕ => ((2:ℝ)/3) ^ l) (1 / (1 - 2/3)) := by
    apply hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hval : (1:ℝ) / (1 - 2/3) = 3 := by norm_num
  rw [hval] at hgeom
  have h3 := hgeom.mul_left ((1:ℝ)/3)
  have hone : (1:ℝ)/3 * 3 = 1 := by norm_num
  rw [hone] at h3
  apply h3.congr_fun
  intro l
  rw [div_pow]
  field_simp
  ring
