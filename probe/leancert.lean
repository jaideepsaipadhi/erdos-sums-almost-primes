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

ANSWERED, and the second half not as predicted.

(a) `norm_num [logPrimeUB]` and `simp only [logPrimeUB]; norm_num` BOTH fail
with unsolved goals; `native_decide` succeeds.  So kernel-clean evaluation is
not available here even at the smallest instance (p = 7, depth 10), and every
numeric step in a leancert-based certificate costs whatever native_decide
costs.

(b) What native_decide costs is NOT `Lean.ofReduceBool`.  Measured, with the
axiom list reassembled inside the runner rather than read off the annotation
channel that had truncated it twice:

    probe_numeric_native = [propext, Classical.choice, Quot.sound,
                            probe_numeric_native._native.native_decide.ax_1_1]

So this toolchain's native_decide mints a PER-DECLARATION axiom named after the
declaration that used it, and `ofReduceBool` appears nowhere (the runner also
emits a direct yes/no on that, and it is NO).

That is a materially better position than the global-axiom framing I had been
assuming, and it changes what Caveat 1.3b would have to say.  A global
`ofReduceBool` is one opaque trust assumption shared by every use, invisible in
the audit once present.  A per-use named axiom is enumerable: `#print axioms`
on any theorem lists exactly which native_decide calls it depends on, by name,
so the trusted base stays countable and the audit in .github/workflows can be
made to fail on an unexpected one.  The trust is still EXTRA -- these are
axioms beyond the three permitted, and they assert the correctness of compiled
evaluation rather than of the kernel -- but it is itemised rather than
wholesale.

(c) probe D (the end-to-end `Real.log 7 <= 2`) still carries `sorryAx`, so it
did not go through even with native_decide on its rational step; its remaining
error was not captured before the annotation cap.  Worth re-running on its own
if the route is ever actually adopted, since D is the shape a real Sodd head
term would take.
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
