/-
PROBE.  Does `leancert` work here, and at what cost to the axiom set?

It is in lake-manifest.json with inherited: true (transitively via Mathlib),
rev 87a21d739dde, and nothing in this development imports it.  Its HEAD needs
toolchain v4.35.0 while this project is on v4.33.0-rc1, so the API I read from
HEAD may not be the API at the pinned rev -- and the anonymous git lane will
not serve that sha, so CI is the only way to find out.

Three questions, in order of decisiveness:

1. Does `import LeanCert` work at all here?
2. Which names exist at the pinned rev?
3. **What axioms does a certificate actually use?**  This is the one that
   matters.  The audits in this repository require exactly
   [propext, Classical.choice, Quot.sound].  LeanCert has 430 uses of
   native_decide, which adds `Lean.ofReduceBool`.  If every usable certificate
   drags that in, adopting this route is a change to what the formalization
   MEANS, not a drop-in.
-/
import LeanCert

-- 2. the names the Sodd head would need
#check @LeanCert.Engine.Chebyshev.Theta.logPrimeUB
#check @LeanCert.Engine.Chebyshev.Theta.log_prime_le_logPrimeUB
#check @LeanCert.Engine.Chebyshev.Theta.theta_le_thetaUB
#check @LeanCert.ANT.mertensLogSum
#check @LeanCert.ANT.mertensLogSum_le_mertensLogSumUpperRat
#check @LeanCert.ANT.verify_mertensLogSum_interval

-- 3a. a KERNEL-mode certificate at trivially small size, and its axioms.
--     `log_prime_le_logPrimeUB` is a proved inequality, so the question is
--     whether the rational side evaluates without the compiler.
theorem probe_kernel_small :
    (if Nat.Prime 7 then Real.log 7 else 0)
      ≤ (LeanCert.Engine.Chebyshev.Theta.logPrimeUB 7 10 : ℝ) :=
  LeanCert.Engine.Chebyshev.Theta.log_prime_le_logPrimeUB 7 10

#print axioms probe_kernel_small

-- 3b. the same bound made numeric, which is where evaluation enters
theorem probe_kernel_numeric :
    (LeanCert.Engine.Chebyshev.Theta.logPrimeUB 7 10 : ℚ) ≤ 2 := by
  decide

#print axioms probe_kernel_numeric
