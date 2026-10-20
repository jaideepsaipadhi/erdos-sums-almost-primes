/-
EXPERIMENT, quarantined.  Everything is settled except ONE question.

Established:
  * leancert v4.33.0 builds here; its API resolves.
  * this development compiles against mathlib v4.33.0 (rc=0), so the pin bump
    is safe and adopting leancert is not a migration.
  * `log_prime_le_logPrimeUB` -- the proved inequality -- costs exactly
    [propext, Classical.choice, Quot.sound].  LeanCert's BOUNDS are clean.
  * `decide` CANNOT evaluate `(logPrimeUB 7 10 : Q) <= 2`.  Depth 10, p = 7;
    as small as it gets, and the kernel still refuses.

The open question is whether that means kernel-clean numerics are impossible,
or whether `decide` was simply the wrong tactic.  `decide` needs the Decidable
instance to whnf-reduce; `norm_num` evaluates rational arithmetic by simp
lemmas instead, and can succeed where reduction will not.  The difference
decides the trust question:

ANSWERED: norm_num and simp BOTH fail with unsolved goals.  native_decide
succeeds.  So kernel-clean numerics are not available here at any size, and
every numeric step costs whatever native_decide costs.  What remains is to
MEASURE that cost rather than assume it -- the previous run's axiom line for
the native case was truncated by Lean's own line wrapping, so `ofReduceBool`
is predicted and not yet confirmed.
-/
import LeanCert

open LeanCert.Engine.Chebyshev.Theta

/-- A: norm_num instead of decide. -/
theorem probe_numeric_normnum : (logPrimeUB 7 10 : ℚ) ≤ 2 := by norm_num [logPrimeUB]

#print axioms probe_numeric_normnum

/-- B: simp with arith, another reduction-free route. -/
theorem probe_numeric_simp : (logPrimeUB 7 10 : ℚ) ≤ 2 := by
  simp only [logPrimeUB]
  norm_num

#print axioms probe_numeric_simp

/-- C: native_decide, which is expected to work and to COST ofReduceBool.
Included so the cost is measured rather than assumed. -/
theorem probe_numeric_native : (logPrimeUB 7 10 : ℚ) ≤ 2 := by native_decide

#print axioms probe_numeric_native

/-- D: the end-to-end shape a Sodd head term would take.  norm_num and simp
both failed on the rational step, so this uses native_decide for it -- which
makes D the measurement of what a REAL certificate costs, not a hoped-for
kernel-clean version. -/
theorem probe_log_seven_le_two : Real.log 7 ≤ 2 := by
  have h := log_prime_le_logPrimeUB 7 10
  have hp : Nat.Prime 7 := by norm_num
  rw [if_pos hp] at h
  have hq : (logPrimeUB 7 10 : ℚ) ≤ 2 := by native_decide
  have hr : ((logPrimeUB 7 10 : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  push_cast at hr
  linarith

#print axioms probe_log_seven_le_two
