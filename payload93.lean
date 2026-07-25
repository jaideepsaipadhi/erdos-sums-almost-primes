/-!
### L2a scaffold

Target: (Fk k s : C) = iteratedDeriv k (Fbig s) 0 / k!

Sub-obligations, in dependency order:

A1  Summability: for 1 < s and |z| < 2^s, the family n -> z^Omega(n) n^(-s)
    is absolutely summable.  NOTE: the naive bound Omega(n) <= log2 n gives
    only |z| < 2^(s-1), which is insufficient near s = 1.  A sharper argument
    is needed (e.g. split n by its 2-adic valuation, or bound the Euler
    product directly).  THIS IS THE OPEN PIECE.

A2  Euler product: with A1, apply Mathlib's eulerProduct_tprod to zOmegaHom
    to get   tprod over primes of (1 - z p^(-s))^(-1) = tsum over n.

A3  Identification: that product equals Fbig s z, i.e.
      prod_p (1 - z p^-s)^-1 = (s-1)^(-z) (1 - z/2^s)^(-1) G2C s z.
    This is the content of the manuscript's section 3.2 / GLW Lemma 11:
    G2 is DEFINED as the regularised tail, so this should reduce to the
    definition of G2C plus the zeta factor.  Check Banksmartin's G2C
    definition (line ~1066) before proving.

A4  Coefficient extraction: F_k(s) (a tsum over k-almost-primes) is the
    k-th Taylor coefficient of z -> tsum_n z^Omega(n) n^(-s).  This is
    where "collect the terms with Omega(n) = k" happens; needs the
    analyticity of the tsum in z on |z| < 2^s.
-/

/-- A1: absolute summability of the z-weighted Dirichlet family. -/
theorem zOmega_summable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Complex.abs z < (2:ℝ) ^ s) :
    Summable (fun n : ℕ => Complex.abs (zOmegaHom s z n)) := by
  sorry

/-- A2: the Euler product for the z-weighted family. -/
theorem zOmega_eulerProduct (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Complex.abs z < (2:ℝ) ^ s) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹) = ∑' n : ℕ, zOmegaHom s z n := by
  sorry

/-- A3: the Euler product equals the factored form Fbig. -/
theorem eulerProduct_eq_Fbig (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Complex.abs z < (2:ℝ) ^ s) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹) = Fbig s z := by
  sorry

/-- A4: F_k is the k-th coefficient of the Dirichlet series. -/
theorem Fk_eq_coeff_tsum (k : ℕ) (s : ℝ) (hs : 1 < s) :
    ((Fk k s : ℝ) : ℂ)
      = iteratedDeriv k (fun z => ∑' n : ℕ, zOmegaHom s z n) 0 / (Nat.factorial k : ℂ) := by
  sorry
