import Banksmartin.Basic

/-!
# The odd Erdos sums

    f_k^odd = sum over odd n >= 3 with Omega(n) = k of 1/(n log n)

CONJECTURE (Lichtman): f_k^odd is strictly decreasing for every k >= 1.

Reuses Banksmartin.Basic wherever the objects are already p >= 3.  The
manuscript's normalisation pulls the p = 2 factor out separately, so cFac,
G2C, dConst and rhoConst there ARE the odd Euler product objects, and DBound,
deltaConv_le, deltaM_abs_le, A2m_le, crit_pos_iff and theorem_7_1 are stated
generically enough to apply unchanged.

GENUINELY NEW, and NOT yet derived on paper:
  * the limit is 1/2, not 1 -- the missing factor (1 - z 2^-s) at z = s = 1
  * hence Proposition 2.5's analogue has a different normalisation
  * the coefficient replacing a_1 = d log2/4 comes from the z = 3^s singularity
  * every certified constant must be recomputed for the p >= 3 product

Numerics in odd/README.md: f_k^odd certified for k = 1..40, strictly
decreasing, tending to 1/2 from above.
-/

open Real BigOperators
noncomputable section

/-- The Erdos sum restricted to odd n. -/
def fOdd (k : ℕ) : ℝ :=
  ∑' n : {n : ℕ // 3 ≤ n ∧ ¬ (2 ∣ n) ∧ bigOmega n = k}, 1 / ((n : ℝ) * Real.log n)

/-- The odd sums tend to 1/2.  Certified numerically to k = 40 (value there is
1/2 + 3.6e-11).  NOT PROVED. -/
theorem fOdd_tendsto_half :
    Filter.Tendsto fOdd Filter.atTop (nhds (1 / 2 : ℝ)) := by
  sorry

/-- THE TARGET.  NOT PROVED. -/
theorem fOdd_decreasing : ∀ k : ℕ, 1 ≤ k → fOdd (k + 1) < fOdd k := by
  sorry

end
