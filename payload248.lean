/-- For a summable family, the partial sum over range (k+1) is the total minus
the indicator tail.  Turns the manuscript's w_k and W_k (defined as indicator
tails) into partial sums of the coefficient identities. -/
theorem sum_range_eq_total_sub_tail {f : ℕ → ℝ} {S : ℝ}
    (hf : HasSum f S) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), f i
      = S - ∑' i : ℕ, (if k < i then f i else 0) := by
  classical
  have hfin : HasSum (fun i : ℕ => if i ∈ Finset.range (k+1) then f i else 0)
      (∑ i ∈ Finset.range (k + 1), f i) := by
    have h0 : HasSum (fun i : ℕ => if i ∈ Finset.range (k+1) then f i else 0)
        (∑ i ∈ Finset.range (k+1), (if i ∈ Finset.range (k+1) then f i else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro i hi
      rw [if_neg hi]
    rwa [Finset.sum_congr rfl (fun i hi => if_pos hi)] at h0
  have hdiff := hf.sub hfin
  have heq : (fun i : ℕ => f i - (if i ∈ Finset.range (k+1) then f i else 0))
      = fun i : ℕ => (if k < i then f i else 0) := by
    funext i
    by_cases h : i ∈ Finset.range (k+1)
    · rw [if_pos h, if_neg (by simp only [Finset.mem_range] at h; omega)]
      ring
    · rw [if_neg h, if_pos (by simp only [Finset.mem_range] at h; omega)]
      ring
  rw [heq] at hdiff
  rw [hdiff.tsum_eq]
  ring
