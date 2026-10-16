/-
PROBE.  Mathlib only, so it answers whether or not Odd/Basic.lean compiles.
The names needed for `g_k -> 1/2`, which section 8 records as proved in the
text but NOT formalized.
-/
import Mathlib

-- geometric decay
#check @tendsto_pow_atTop_nhds_zero_of_lt_one
-- polynomial times geometric
#check @tendsto_pow_mul_geometric_of_norm_lt_one
-- squeeze, eventually form
#check @squeeze_zero'
#check @squeeze_zero
-- getting from |f - a| -> 0 back to f -> a
#check @tendsto_iff_norm_sub_tendsto_zero
#check @tendsto_zero_iff_abs_tendsto_zero

/- The two limits, in the exact shapes the proof needs. -/
example : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2) ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

example : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 3 * ((1:ℝ)/3) ^ n)
    Filter.atTop (nhds 0) :=
  tendsto_pow_mul_geometric_of_norm_lt_one 3 (by rw [Real.norm_eq_abs]; norm_num)

/- and the final step, on an arbitrary real sequence -/
example (f : ℕ → ℝ) (a : ℝ)
    (h : Filter.Tendsto (fun k => |f k - a|) Filter.atTop (nhds 0)) :
    Filter.Tendsto f Filter.atTop (nhds a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using h
