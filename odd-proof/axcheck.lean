-- Axiom audit for the odd development.  Run:  lake env lean odd-proof/axcheck.lean
-- Every line must report exactly [propext, Classical.choice, Quot.sound].
import Odd.Basic
#print axioms fOdd_decreasing
#print axioms fOdd_tendsto_half
#print axioms fOdd_decreasing_of_facts
#print axioms fOdd_expansion_final
#print axioms oddDiff_integrable
#print axioms oddNear_integral_bound
#print axioms fOdd_u_form
#print axioms jacobian_u_signed
#print axioms eps_of_u_signed
#print axioms hCoeff_taylor
#print axioms zetaRegFull_analyticAt_one
#print axioms zeta_laurent_constant
#print axioms integral_substitute
#print axioms jacobian_signed
#print axioms eps_zeta_uniform
#print axioms prime_three_differentiableOn_three
#print axioms Hodd_differentiableOn_three
#print axioms HoddTildeFactored_differentiableOn
#print axioms hCoeff_sum_one_uncond
#print axioms hCoeff_sum_two_uncond
#print axioms hCoeff_eq_cauchy_coeff
#print axioms hCoeff_eq_circleIntegral
