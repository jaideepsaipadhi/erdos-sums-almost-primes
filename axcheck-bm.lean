-- Axiom audit for the unrestricted development.  Run:
--   lake env lean axcheck-bm.lean
-- Every line must report exactly [propext, Classical.choice, Quot.sound].
-- A `sorryAx` here means a declaration below depends on an errored or
-- unfinished proof, which a green `lake build` alone does not rule out for
-- any particular theorem -- the build only reports that SOMETHING compiled.
import Banksmartin.Basic

-- the main theorems
#print axioms erdos_sums_increase_from_six
#print axioms erdos_sums_increase_from_six'

-- the Tier A lemmas that left the trusted base
#print axioms phiBound_mono_of_bounds
#print axioms phiBound_pos_at_2440

-- the Tier C field that left the trusted base: d
#print axioms prod_le_hasProd_of_one_le
#print axioms dConst_factor_sub_one
#print axioms dConst_factor_one_le
#print axioms dConst_lower_bound
#print axioms aOneConst_ge
#print axioms dConst_lower_bound_sharp

