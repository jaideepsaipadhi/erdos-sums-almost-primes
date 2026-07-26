theorem tail_regroup (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3/2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p:ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p:ℕ):ℝ) ^ (-s))⁻¹))) :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * ((((p:ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = ((cFac s : ℝ) : ℂ) ^ z * G2C s z :=
  (tail_regroup_hasProd s hs z (by linarith) hc hmulR hposR hlogR).tprod_eq
