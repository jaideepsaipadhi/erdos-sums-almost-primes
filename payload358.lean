/-- cBracket fs s z -> cBracket fs 1 z as s -> 1 from above.
Same bridge as G2C_tendsto_at_one: continuity on the subtype {s // 1 <= s}
gives the limit along nhdsWithin 1 (Ici 1), and nhdsWithin 1 (Ioi 1) is finer. -/
theorem cBracket_tendsto_at_one (fs : ℝ) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Filter.Tendsto (fun s : ℝ => cBracket fs s z) (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (cBracket fs 1 z)) := by
  have hmem : (1:ℝ) ∈ Set.Ici (1:ℝ) := Set.mem_Ici.mpr (le_refl 1)
  have hcont := cBracket_continuous_s fs z hz
  have hsub : Filter.Tendsto ((Set.Ici (1:ℝ)).restrict (fun s : ℝ => cBracket fs s z))
      (nhds (⟨(1:ℝ), hmem⟩ : ↑(Set.Ici (1:ℝ)))) (nhds (cBracket fs 1 z)) := by
    exact hcont.continuousAt
  have hIci := (tendsto_nhdsWithin_iff_subtype hmem (fun s : ℝ => cBracket fs s z)
    (nhds (cBracket fs 1 z))).mpr hsub
  apply hIci.mono_left
  apply nhdsWithin_mono
  intro x hx
  exact le_of_lt (Set.mem_Ioi.mp hx)
