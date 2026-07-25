theorem log_tprod_real {ι : Type*} {f : ι → ℝ} (hpos : ∀ i, 0 < f i)
    (hmul : Multipliable f) (hlog : Summable (fun i => Real.log (f i))) :
    Real.log (∏' i : ι, f i) = ∑' i : ι, Real.log (f i) := by
  have hpart : ∀ t : Finset ι, ∏ i ∈ t, f i
      = Real.exp (∑ i ∈ t, Real.log (f i)) := by
    intro t
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.exp_log (hpos i)]
  have h1 : HasProd f (∏' i : ι, f i) := hmul.hasProd
  have h2 : HasSum (fun i => Real.log (f i)) (∑' i : ι, Real.log (f i)) := hlog.hasSum
  have h3 : HasProd f (Real.exp (∑' i : ι, Real.log (f i))) := by
    have hcomp := (Real.continuous_exp.tendsto _).comp h2
    apply hcomp.congr
    intro t
    rw [Function.comp_apply, ←  hpart t]
  have heq : (∏' i : ι, f i) = Real.exp (∑' i : ι, Real.log (f i)) :=
    h1.unique h3
  rw [heq, Real.log_exp]
