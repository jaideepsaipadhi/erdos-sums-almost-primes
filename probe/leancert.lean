/-
EXPERIMENT, quarantined on its own branch.  Not imported by the library.

Question: can an INSTANCE of the NumericalFacts structures be built here, and
what does it cost the axiom set?

`leancert` is pinned in lake-manifest.json at tag v4.32.1
(87a21d739dde0531c0363f9257b12022836372d1), inherited transitively.  At that
rev the modules we would need -- ANT/Mertens.lean, Engine/Chebyshev/Theta.lean,
ANT/Abel.lean -- all exist with ZERO sorries.  Names below are taken from that
tag, not from HEAD: the namespace is `LeanCert.Engine.ChebyshevTheta` at
v4.32.1 and `LeanCert.Engine.Chebyshev.Theta` at HEAD, so HEAD's names would
have been wrong.

Three things to learn, in order:

1. Does leancert's source compile under THIS toolchain?  Its own lean-toolchain
   says v4.32.0; this project is v4.33.0-rc1, and Lake builds dependencies from
   source with the root's toolchain, so the question is whether it survives the
   Mathlib API drift between those versions.
2. Do the names resolve?
3. **What axioms does a bound actually use?**  `log_prime_le_logPrimeUB` is an
   ordinary proved inequality, so it should cost nothing beyond the usual
   three.  The numeric step is where evaluation -- and possibly
   `Lean.ofReduceBool` via native_decide -- enters.  Where exactly that
   boundary falls decides how much of a future instance can stay in the kernel.
-/
import LeanCert

open LeanCert.Engine.ChebyshevTheta

#check @LeanCert.Engine.ChebyshevTheta.logPrimeUB
#check @LeanCert.Engine.ChebyshevTheta.log_prime_le_logPrimeUB
#check @LeanCert.Engine.ChebyshevTheta.theta_le_thetaUB
#check @LeanCert.ANT.mertensLogSum
#check @LeanCert.ANT.mertensLogSum_le_mertensLogSumUpperRat
#check @LeanCert.ANT.verify_mertensLogSum_interval

/-- The proved inequality on its own: no evaluation, so this should be clean. -/
theorem probe_bound_only :
    (if Nat.Prime 7 then Real.log 7 else 0 : ℝ) ≤ (logPrimeUB 7 10 : ℝ) :=
  log_prime_le_logPrimeUB 7 10

#print axioms probe_bound_only

/-- The numeric step, in the kernel.  If `decide` manages this at depth 10,
the rational side is kernel-reachable at small sizes. -/
theorem probe_numeric_kernel : (logPrimeUB 7 10 : ℚ) ≤ 2 := by decide

#print axioms probe_numeric_kernel

/-- Chained: a numeric upper bound on `log 7` with no `native_decide` anywhere.
This is the shape every head-term bound in a future Sodd certificate would
take, so its axiom set is the one that matters. -/
theorem probe_log_seven_le_two : Real.log 7 ≤ 2 := by
  have h := log_prime_le_logPrimeUB 7 10
  have hp : Nat.Prime 7 := by norm_num
  rw [if_pos hp] at h
  have hq : (logPrimeUB 7 10 : ℚ) ≤ 2 := by decide
  have hr : ((logPrimeUB 7 10 : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  push_cast at hr
  linarith

#print axioms probe_log_seven_le_two
