/-!
### A4 scaffold: F_k is the k-th Taylor coefficient of the Dirichlet series

Target:  (Fk k s : C) = iteratedDeriv k (fun z => sum' n, zOmegaHom s z n) 0 / k!

Route (term-by-term differentiation, k times):

Mathlib provides, in Analysis/Complex/LocallyUniformLimit.lean:
  differentiableOn_tsum_of_summable_norm  (line 171)
  hasSum_deriv_of_summable_norm           (line 182)
both taking: a summable bound u, termwise DifferentiableOn on an open U,
and ||F i w|| <= u i on U.  We use U = ball 0 (3/2), where A1's
zOmega_summable supplies the bound.

Sub-obligations:

C1  bound_summable j : for each j, the family
      n -> (Omega n)^j * (3/2)^(Omega n) * n^(-s)
    is summable.  (Polynomial factors do not break convergence because
    |z| = 3/2 < 2^s for s > 1; same comparison as A1 with a polynomial
    correction.)  THIS IS THE ANALYTIC INPUT.

C2  deriv_termwise j : the j-th iterated derivative of the tsum is the
    tsum of the j-th derivatives, on ball 0 (3/2).
    By induction on j using hasSum_deriv_of_summable_norm with C1.

C3  deriv_monomial_at_zero : iteratedDeriv k (fun z => z^m * c) 0
      = if m = k then k! * c else 0.
    Elementary; the collapse that picks out Omega n = k.

A4 follows: apply C2 at j = k, evaluate at 0 with C3, and the surviving
terms are exactly those with Omega n = k, i.e. Fk k s.
-/

/-- C1: the polynomially-weighted family is summable. -/
theorem omega_pow_summable (s : ℝ) (hs : 1 < s) (j : ℕ) :
    Summable (fun n : ℕ => ((bigOmega n : ℕ) : ℝ) ^ j * (3/2) ^ (bigOmega n) * ((n:ℝ) ^ (-s))) := by
  sorry

/-- C3: the k-th derivative of a monomial at 0. -/
theorem iteratedDeriv_monomial_zero (m k : ℕ) (c : ℂ) :
    iteratedDeriv k (fun z : ℂ => z ^ m * c) 0
      = if m = k then (Nat.factorial k : ℂ) * c else 0 := by
  sorry
