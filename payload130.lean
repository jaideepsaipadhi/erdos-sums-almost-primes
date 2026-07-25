/-!
### A3 scaffold: the Euler product equals Fbig

The identity (verified numerically to 12+ digits):
  prod_p (1 - z p^-s)^-1  =  (cFac s)^z * (1 - z 2^-s)^-1 * G2C s z

with cFac s = prod_{p>=3} (1 - p^-s)^-1 and
G2C s z = prod_{p>=3} (1 - z p^-s)^-1 (1 - p^-s)^z.

MATHLIB GAP: neither log-of-tprod nor cpow-of-tprod exists in this pin,
so B1 below must be built.  Route: multipliability + positivity gives
HasProd, and log is continuous, so log of the limit is the limit of the
log partial sums.

Sub-obligations:

B1  log_tprod_real : for a multipliable family of positive reals,
    log (prod' f) = sum' (log o f).           [THE MATHLIB GAP]

B2  cFac_cpow : (cFac s : C)^z = exp (z * sum'_{p>=3} log ((1 - p^-s)^-1)).
    From B1 and the definition of cpow for a positive real base.

B3  tail_regroup : prod'_{p>=3} (1 - z p^-s)^-1
      = (cFac s)^z * G2C s z,
    i.e. the regularising factors telescope.  Uses B2 and multipliability
    of both tail families.

B4  split_two : prod'_p (1 - z p^-s)^-1
      = (1 - z 2^-s)^-1 * prod'_{p>=3} (1 - z p^-s)^-1.
    Splitting the prime tprod at p = 2.

A3 follows from B3 and B4 by unfolding Fbig.
-/

/-- B1: log of an infinite product of positives is the sum of logs. -/
theorem log_tprod_real {f : ℕ → ℝ} (hpos : ∀ i, 0 < f i)
    (hmul : Multipliable f) (hlog : Summable (fun i => Real.log (f i))) :
    Real.log (∏' i : ℕ, f i) = ∑' i : ℕ, Real.log (f i) := by
  sorry

/-- B2: the cFac factor as an exponential. -/
theorem cFac_cpow (s : ℝ) (hs : 1 < s) (z : ℂ) :
    ((cFac s : ℝ) : ℂ) ^ z
      = Complex.exp (z * ((Real.log (cFac s) : ℝ) : ℂ)) := by
  sorry

/-- B3: the p >= 3 tail regroups into cFac^z times G2C. -/
theorem tail_regroup (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3/2) :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (1 - z * (((p:ℕ):ℝ) ^ (-s) : ℝ))⁻¹)
      = ((cFac s : ℝ) : ℂ) ^ z * G2C s z := by
  sorry

/-- B4: split the prime product at p = 2. -/
theorem split_two (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3/2) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹)
      = (1 - z * (((2:ℕ):ℝ) ^ (-s) : ℝ))⁻¹
        * ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (1 - z * (((p:ℕ):ℝ) ^ (-s) : ℝ))⁻¹ := by
  sorry
