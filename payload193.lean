theorem Fk_eq_coeff_Fbig (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))) :
    ((Fk k s : ℝ) : ℂ)
      = (iteratedDeriv k (fun z => Fbig s z) 0) / (Nat.factorial k : ℂ) := by
  have hA4 := Fk_eq_coeff_tsum k hk s hs
  rw [hA4]
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hball : Metric.ball (0:ℂ) (3/2) ∈ nhds (0:ℂ) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, dist_self]
    norm_num
  filter_upwards [hball] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzle : Norm.norm z ≤ 3/2 := le_of_lt hz
  have hsum := zOmega_summable s hs z hzle
  have hA2 := zOmega_eulerProduct s hs z hsum
  have hA3 := eulerProduct_eq_Fbig s hs z hzle hc hmulR hposR hlogR
  rw [← hA2, hA3]
