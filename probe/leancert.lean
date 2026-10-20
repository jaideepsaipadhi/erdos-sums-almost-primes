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

  * norm_num works  -> the whole route can stay in the kernel, and
    `Lean.ofReduceBool` is never needed.  Adopting leancert costs nothing in
    trust.
  * norm_num fails too -> every numeric step needs native_decide, and adopting
    it means accepting ofReduceBool.  Caveat 1.3b would have to be rewritten.
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

/-- D: the end-to-end shape a Sodd head term would take, via whichever of the
above works.  If this comes back on the three permitted axioms, the route is
kernel-clean end to end. -/
theorem probe_log_seven_le_two : Real.log 7 ≤ 2 := by
  have h := log_prime_le_logPrimeUB 7 10
  have hp : Nat.Prime 7 := by norm_num
  rw [if_pos hp] at h
  have hq : (logPrimeUB 7 10 : ℚ) ≤ 2 := by norm_num [logPrimeUB]
  have hr : ((logPrimeUB 7 10 : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  push_cast at hr
  linarith

#print axioms probe_log_seven_le_two
