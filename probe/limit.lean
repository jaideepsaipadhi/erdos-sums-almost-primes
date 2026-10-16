/-
PROBE.  Mathlib only.  The name question is SETTLED:
  summable_pow_mul_geometric_of_norm_lt_one  exists (NormedRing + HasSummableGeomSeries)
  Summable.tendsto_atTop_zero                exists
  tendsto_pow_mul_geometric_of_norm_lt_one   does NOT
  abs_add                                    does NOT
What remains is only cost, so this keeps one check: the pow monotonicity lemma
that would have made the cubic bound a one-liner, recorded for next time.
-/
import Mathlib

#check @pow_le_pow_left
#check @abs_add_le
#check @norm_add_le

example : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 3 * ((1:ℝ)/3) ^ n)
    Filter.atTop (nhds 0) :=
  (summable_pow_mul_geometric_of_norm_lt_one 3
    (by rw [Real.norm_eq_abs]; rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)];
        norm_num)).tendsto_atTop_zero
