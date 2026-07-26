/-- The residue, restricted to the right half-plane (where our real s lives). -/
theorem zeta_residue_halfplane :
    Filter.Tendsto (fun z : ℂ => (z - 1) * riemannZeta z)
      (nhdsWithin 1 {z : ℂ | 1 < z.re}) (nhds 1) := by
  apply Filter.Tendsto.mono_left riemannZeta_residue_one
  apply nhdsWithin_mono
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcon
  rw [hcon] at hz
  simp at hz
