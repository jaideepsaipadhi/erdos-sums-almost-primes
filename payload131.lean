theorem log_tprod_real {f : ℕ → ℝ} (hpos : ∀ i, 0 < f i)
    (hmul : Multipliable f) (hlog : Summable (fun i => Real.log (f i))) :
    Real.log (∏' i : ℕ, f i) = ∑' i : ℕ, Real.log (f i) := by
  have hpart : ∀ n : ℕ, ∏ i ∈ Finset.range n, f i
      = Real.exp (∑ i ∈ Finset.range n, Real.log (f i)) := by
    intro n
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.exp_log (hpos i)]
  have htend1 : Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, f i)
      Filter.atTop (nhds (∏' i : ℕ, f i)) := hmul.hasProd.tendsto_prod_nat
  have htend2 : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, Real.log (f i))
      Filter.atTop (nhds (∑' i : ℕ, Real.log (f i))) := hlog.hasSum.tendsto_sum_nat
  have htend3 : Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, f i)
      Filter.atTop (nhds (Real.exp (∑' i : ℕ, Real.log (f i)))) := by
    have hcomp := (Real.continuous_exp.tendsto _).comp htend2
    apply hcomp.congr
    intro n
    rw [Function.comp_apply, ←  hpart n]
  have heq : (∏' i : ℕ, f i) = Real.exp (∑' i : ℕ, Real.log (f i)) :=
    tendsto_nhds_unique htend1 htend3
  rw [heq, Real.log_exp]
