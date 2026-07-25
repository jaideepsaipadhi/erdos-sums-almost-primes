/-- A1 step 3a: the scaled prime sum converges. -/
theorem zOmega_prime_sum_summable (s : ℝ) (hs : 1 < s) (z : ℂ) :
    Summable (fun p : Nat.Primes => Norm.norm z * ((p:ℝ) ^ (-s))) := by
  have hbase : Summable (fun p : Nat.Primes => ((p:ℝ) ^ (-s))) := by
    rw [Nat.Primes.summable_rpow]
    linarith
  exact hbase.mul_left _
