/-- G2C s z -> G2C 1 z as s -> 1 from above.
G2C_continuous_s gives continuity on the subtype {s // 1 <= s}; the bridge
tendsto_nhdsWithin_iff_subtype converts that to a limit along nhdsWithin 1
(Ici 1), and nhdsWithin 1 (Ioi 1) is finer. -/
theorem G2C_tendsto_at_one (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Filter.Tendsto (fun s : ℝ => G2C s z) (nhdsWithin 1 (Set.Ioi (1:ℝ)))
      (nhds (G2C 1 z)) := by
  have hmem : (1:ℝ) ∈ Set.Ici (1:ℝ) := le_refl 1
  have hcont := G2C_continuous_s z hz
  have hsub : Filter.Tendsto (Set.Ici (1:ℝ)).restrict (fun s : ℝ => G2C s z)
      (nhds (⟨ (1:ℝ), hmem ⟩)) (nhds (G2C 1 z)) := by
    have := hcont.continuousAt (x := ⟨(1:ℝ), hmem⟩)
    exact this
  have hIci := (tendsto_nhdsWithin_iff_subtype hmem (fun s : ℝ => G2C s z)
    (nhds (G2C 1 z))).mpr hsub
  apply hIci.mono_left
  apply nhdsWithin_mono
  intro x hx
  exact le_of_lt hx
