
MANUSCRIPT RECEIVED (banks-martin-proof.pdf, in repo /docs if committed): the
complete spec. FORMALIZATION ROADMAP (three tiers):
T1 (target, closes manuscript Caveat 8.1a): formalize the six pages of human
   proofs — Lem 2.1 (= lemma1_foundation, DONE), eq (2) (= criterion, DONE),
   Lem 2.2 exact expansion, Lem 2.4 exactness I'_k = sum c_i 2^{i-k} A_{k-i},
   Prop 2.5 assembly identity (6), Thm 4.1 two-sided delta bound, Thm 6.1
   refined E1 enclosure, Thm 7.1 far range k>=2440.
T2 (the wall inside T1): Thm 4.1 needs gap-5 integral identity + Euler's
   gamma = -int e^{-u} log u du. CHECK MATHLIB FIRST: Real.Gamma deriv at 1,
   exponential integral. Mitigation: only the UPPER delta bound is needed and
   aE1(a) <= e^{-a} may be provable from the defining integral directly.
T3 (do NOT formalize): Arb computations (delta-table, prime tails, box sweeps,
   arc sups) stay as NumericalFacts hypothesis = trusted computing base, per
   manuscript Caveat 1.3b. dConst, rhoConst now genuinely defined; still to
   define as real objects: SstarConst (sum 2^i |c_i| — needs c_i := taylor
   coeff of G2(1,z), i.e. formalize G2 first), alphaConst, GammaConst (deriv
   sups). Defining G2 and c_i in Lean is the natural session opener — it
   unlocks Lem 2.2/2.4/Prop 2.5 statements simultaneously.
END STATE: Lean-verified reduction + Arb-certified hypothesis = machine-checked
conditional theorem, trust surface = FLINT/Arb only.
