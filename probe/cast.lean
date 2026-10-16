/-
PROBE.  Imports Mathlib only, so it answers even while Odd/Basic.lean fails to
compile.  The question: `exact_mod_cast` will not carry
`(95880679/10000000 : ℚ) < harmonic 8191` across to ℝ, and I have guessed twice
at why.  These #checks settle what `harmonic` actually is and which cast lemma
applies, so the next edit is informed rather than a third guess.
-/
import Mathlib

#check @harmonic
#check @Real.eulerMascheroniSeq
#check @Real.eulerMascheroniSeq_lt_eulerMascheroniConstant
#check @Rat.cast_lt
#check @Rat.cast_div
#check @Rat.cast_lt_cast

-- does the cast go through at a trivial size, in the exact shape used?
example (h : (3 / 2 : ℚ) < harmonic 4) : (3 / 2 : ℝ) < (harmonic 4 : ℝ) := by
  exact_mod_cast h

-- and via the explicit route
example (h : (3 / 2 : ℚ) < harmonic 4) : (3 / 2 : ℝ) < (harmonic 4 : ℝ) := by
  have h2 : ((3 / 2 : ℚ) : ℝ) < ((harmonic 4 : ℚ) : ℝ) := Rat.cast_lt.mpr h
  push_cast at h2
  exact h2
