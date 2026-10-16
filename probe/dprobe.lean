/-
PROBE, not a result.  Not imported by the library; CI runs it with `|| true`,
so its output is the point and it cannot fail the build.

The library attempt alongside this probe raises `simp`'s step budget to get a
668-element `Finset` literal evaluated.  That may simply work -- 223,000
rewrites is not a wall, just past the 100,000 default.  But the literal is
QUADRATIC by construction (pairwise dedup on insert), so if 668 is near the
edge then nothing larger will ever go through, and the right construction is
a `List`-backed `Finset`: `Finset.mk` on a `Multiset` coerced from a list,
with `Nodup` discharged once, which makes evaluation LINEAR in the factors.

These #checks establish whether that route's names exist, so that if the
budget raise fails there is no second blind run.
-/
import Banksmartin.Basic

-- the List-backed Finset route
#check @Finset.prod_mk
#check @Multiset.coe_nodup
#check @List.prod_cons
#check @List.Sorted.nodup
#check @Finset.prod_subtype_eq_prod_filter

-- cheap Nodup: a strictly sorted list is nodup, and sortedness is O(n)
#check @List.Pairwise
#check @List.chain'_iff_pairwise

/- The shape, at two elements: a Finset built from a list plus a Nodup proof,
   with its product evaluated through Finset.prod_mk rather than prod_insert. -/
example :
    (∏ p ∈ (⟨(([⟨3, by norm_num⟩, ⟨5, by norm_num⟩] :
                List {p : ℕ // p.Prime ∧ 3 ≤ p}) : Multiset _), by decide⟩ :
              Finset {p : ℕ // p.Prime ∧ 3 ≤ p}),
      (1 + 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2))))
      = (4 / 3) * (16 / 15) := by
  rw [Finset.prod_mk]
  norm_num
