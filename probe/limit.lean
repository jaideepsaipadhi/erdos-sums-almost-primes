/-
PROBE.  Mathlib only.  Two names were wrong: `abs_add` and
`tendsto_pow_mul_geometric_of_norm_lt_one`.  The triangle inequality is now
routed around entirely in the library proof, so the only open question is how
this Mathlib spells "a polynomial times a geometric tends to zero".
-/
import Mathlib

-- candidates for n^k * r^n -> 0
#check @tendsto_pow_mul_geometric_of_norm_lt_one
#check @tendsto_pow_mul_geometric_of_norm_lt_1
#check @summable_pow_mul_geometric_of_norm_lt_one
#check @summable_pow_mul_geometric_of_norm_lt_1
#check @tendsto_self_mul_const_pow_of_lt_one
#check @isLittleO_pow_const_const_pow_of_one_lt
#check @Summable.tendsto_atTop_zero

-- triangle inequality, for the record
#check @abs_add
#check @abs_add_le
#check @norm_add_le
#check @abs_sub_abs_le_abs_sub

-- the pieces the library proof actually uses, in shape
#check @abs_le
#check @neg_abs_le
#check @le_abs_self

/- Does the summability route give the limit? -/
example : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 3 * ((1:ℝ)/3) ^ n)
    Filter.atTop (nhds 0) :=
  (summable_pow_mul_geometric_of_norm_lt_one 3
    (by rw [Real.norm_eq_abs]; rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)];
        norm_num)).tendsto_atTop_zero
