/-
PROBE, not a result.  Not imported by the library; run by CI with
`lake env lean probe/dprobe.lean`, which reports every command independently,
so one run says which Mathlib names exist and which proof route closes.

The question: `dConst` is (1/4) times a tprod over primes p >= 3 of factors
that `dConst_family_multipliable`'s own `hexact` shows equal 1 + 1/(p(p-2)).
Every factor exceeds 1, so a FINITE partial product is a lower bound on the
whole product -- with no tail estimate at all.  66 primes (p <= 331) suffice
for the bound the unrestricted theorem actually uses.  What is unknown from
outside the runner is how Mathlib spells "partial product <= total product"
for ℝ, which is not an OrderedCommMonoid under multiplication.
-/
import Banksmartin.Basic

-- 1. the ordering lemmas for infinite products
#check @Finset.prod_le_hasProd
#check @Finset.prod_le_tprod
#check @one_le_tprod
#check @Real.one_le_tprod

-- 2. finite products of factors >= 1
#check @Finset.one_le_prod
#check @Finset.one_le_prod'
#check @Finset.prod_sdiff
#check @Finset.prod_subset

-- 3. getting from Multipliable to HasProd, and the limit route
#check @Multipliable.hasProd
#check @HasProd
#check @ge_of_tendsto
#check @ge_of_tendsto'
#check @Filter.eventually_atTop

-- 4. what the repo already has
#check @dConst_family_multipliable
#check @dConst_prod_eq_subtype
#check @dConst
#check @aOneConst_ge_of_d

/- ROUTE A: the direct Mathlib lemma, if it applies to ℝ. -/
example (ι : Type) (s : Finset ι) (f : ι → ℝ) (a : ℝ)
    (h1 : ∀ i, 1 ≤ f i) (hp : HasProd f a) : ∏ i ∈ s, f i ≤ a :=
  Finset.prod_le_hasProd s (fun i _ => h1 i) hp

/- ROUTE B: by hand from the net definition, if Route A does not apply.
   For any finite t containing s, prod over t = prod over t\s * prod over s
   >= prod over s, so the net is eventually >= prod over s. -/
example (ι : Type) (s : Finset ι) (f : ι → ℝ) (a : ℝ)
    (h1 : ∀ i, 1 ≤ f i) (hp : HasProd f a) : ∏ i ∈ s, f i ≤ a := by
  have hnet : Filter.Tendsto (fun t : Finset ι => ∏ i ∈ t, f i) Filter.atTop (nhds a) := hp
  refine ge_of_tendsto hnet ?_
  filter_upwards [Filter.eventually_ge_atTop s] with t hst
  have hsplit : (∏ i ∈ t \ s, f i) * (∏ i ∈ s, f i) = ∏ i ∈ t, f i :=
    Finset.prod_sdiff hst
  have hcompl : (1 : ℝ) ≤ ∏ i ∈ t \ s, f i :=
    Finset.one_le_prod (fun i _ => h1 i)
  have hs0 : (0 : ℝ) ≤ ∏ i ∈ s, f i :=
    Finset.prod_nonneg (fun i _ => le_trans zero_le_one (h1 i))
  nlinarith [hsplit, hcompl, hs0]

/- The explicit finite set, and whether the kernel will evaluate a product
   over it.  Two primes only here -- if this shape works, 66 is mechanical. -/
example : True := by
  have hs : Finset {p : ℕ // p.Prime ∧ 3 ≤ p} :=
    {⟨3, by norm_num⟩, ⟨5, by norm_num⟩}
  trivial

/- And whether a product over such a literal set evaluates. -/
example :
    (∏ p ∈ ({⟨3, by norm_num⟩, ⟨5, by norm_num⟩} :
              Finset {p : ℕ // p.Prime ∧ 3 ≤ p}),
      (1 + 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2))))
      = (4 / 3) * (16 / 15) := by
  norm_num [Finset.prod_insert, Finset.mem_singleton]
