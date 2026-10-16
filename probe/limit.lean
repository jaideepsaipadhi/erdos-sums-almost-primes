/-
PROBE, cost edition.  The name question is settled; the problem is COST.
`summable_pow_mul_geometric_of_norm_lt_one` timed out at the 200000 default in
the probe itself, and at 2000000 inside the library, so it is expensive
wherever it is used and raising the limit only buys a slower failure.

Each candidate below gets its own heartbeat ceiling.  The ones that compile
are affordable; the ones that time out name their own ceiling in the error, so
one run gives a cost ranking rather than a yes/no.
-/
import Mathlib

#check @isLittleO_pow_const_const_pow_of_one_lt
#check @Asymptotics.IsLittleO.tendsto_div_nhds_zero
#check @tendsto_pow_atTop_nhds_zero_of_lt_one

-- A: the summable route, with the norm side condition pulled out and simplified
set_option maxHeartbeats 400000 in
example : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 3 * ((1:ℝ)/3) ^ n)
    Filter.atTop (nhds 0) := by
  have hr : ‖((1:ℝ)/3)‖ < 1 := by
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg]; · norm_num
    · norm_num
  exact (summable_pow_mul_geometric_of_norm_lt_one 3 hr).tendsto_atTop_zero

-- B: same, but let norm_num do the whole side condition
set_option maxHeartbeats 400000 in
example : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 3 * ((1:ℝ)/3) ^ n)
    Filter.atTop (nhds 0) := by
  have hr : ‖((1:ℝ)/3)‖ < 1 := by norm_num [Real.norm_eq_abs]
  exact (summable_pow_mul_geometric_of_norm_lt_one 3 hr).tendsto_atTop_zero

-- C: the little-o route, which avoids summability machinery entirely
set_option maxHeartbeats 400000 in
example : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 3 / (3:ℝ) ^ n)
    Filter.atTop (nhds 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt 3 (by norm_num : (1:ℝ) < 3)).tendsto_div_nhds_zero

-- D: is the summability itself the cost, or the tendsto step?
set_option maxHeartbeats 400000 in
example : Summable (fun n : ℕ => ((n : ℝ)) ^ 3 * ((1:ℝ)/3) ^ n) := by
  have hr : ‖((1:ℝ)/3)‖ < 1 := by norm_num [Real.norm_eq_abs]
  exact summable_pow_mul_geometric_of_norm_lt_one 3 hr

-- E: plain geometric, for a baseline cost
set_option maxHeartbeats 400000 in
example : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/3) ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
