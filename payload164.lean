theorem eulerProduct_eq_Fbig (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3/2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹) = Fbig s z := by
  have hmul3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) :=
    (tail_regroup_hasProd s hs z (by linarith) hc hmulR hposR hlogR).multipliable
  rw [split_two s hs z hz hmul3]
  rw [tail_regroup s hs z hz hc hmulR hposR hlogR]
  unfold Fbig
  have h2 : ((2:ℂ) ^ (s:ℂ)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro hcon
    exact absurd hcon.1 (by norm_num)
  have hbridge : (1 - z * (((2:ℕ):ℝ) ^ (-s) : ℝ))⁻¹
      = (1 - z / ((2:ℂ) ^ (s:ℂ)))⁻¹ := by
    congr 1
    congr 1
    have hreal : (((2:ℕ):ℝ) ^ (-s) : ℝ) = ((2:ℝ) ^ s)⁻¹ := by
      norm_num
      rw [Real.rpow_neg (by norm_num)]
    rw [hreal]
    have hcast : (((((2:ℝ) ^ s)⁻¹ : ℝ)) : ℂ) = ((2:ℂ) ^ (s:ℂ))⁻¹ := by
      rw [Complex.ofReal_inv]
      congr 1
      rw [← Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hcast]
    field_simp
  rw [hbridge]
  ring
