/-- G2manu s z -> G2at1 z as s -> 1 from above.
Product of kappa_cpow_tendsto and G2C_tendsto_at_one, since
G2manu s z = kappa(s)^z * G2C s z and G2at1 z = (1/2)^z * G2C 1 z. -/
theorem G2manu_tendsto_G2at1 (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Filter.Tendsto (fun s : ℝ => G2manu s z) (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (G2at1 z)) := by
  have hprod := (kappa_cpow_tendsto z).mul (G2C_tendsto_at_one z hz)
  have hval : G2at1 z = (((1/2 : ℝ)) : ℂ) ^ z * G2C 1 z := rfl
  rw [hval]
  apply hprod.congr
  intro s
  unfold G2manu
  ring
