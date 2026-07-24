import PrimeNumberTheoremAnd.IEANTN.Mertens
import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

open Real BigOperators

noncomputable section

/-- Ω(n): number of prime factors of n with multiplicity. -/
def bigOmega (n : ℕ) : ℕ := (Nat.factorization n).sum (fun _ e => e)

def f (k : ℕ) : ℝ :=
  ∑' n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k}, 1 / ((n : ℝ) * Real.log n)

/-- Every n ≥ 1 satisfies 2^(Ω(n)) ≤ n (strong induction via the minimal
    prime factor: n = p * m with p ≥ 2 prime, Ω(n) = Ω(m) + 1, m < n). -/
lemma pow_bigOmega_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ bigOmega n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _hn => simp [bigOmega]
    | (n + 2), _ =>
      set N := n + 2 with hN
      have hN2 : 2 ≤ N := by omega
      set p := N.minFac with hp
      have hp_prime : p.Prime := Nat.minFac_prime (by omega)
      have hp_dvd : p ∣ N := Nat.minFac_dvd N
      obtain ⟨m, hm⟩ := hp_dvd
      have hp2 : 2 ≤ p := hp_prime.two_le
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso; rw [h0, mul_zero] at hm; omega
        · exact h0
      have hmN : m < N := by
        rw [hm]; nlinarith
      have hbO : bigOmega N = bigOmega m + 1 := by
        have hpne : p ≠ 0 := hp_prime.pos.ne'
        have hmne : m ≠ 0 := by omega
        have hfact : N.factorization = p.factorization + m.factorization := by
          rw [hm, Nat.factorization_mul hpne hmne]
        have hpfact : p.factorization = Finsupp.single p 1 := by
          rw [hp_prime.factorization]
        unfold bigOmega
        rw [hfact, hpfact]
        rw [Finsupp.sum_add_index' (by simp) (by simp)]
        rw [Finsupp.sum_single_index (by simp)]
        ring
      rw [hbO, pow_succ]
      have := ih m hmN hm1
      calc 2 ^ bigOmega m * 2 ≤ m * p := by
            apply Nat.mul_le_mul this hp2
        _ = N := by rw [hm]; ring

/-- Every k-almost-prime n ≥ 2 satisfies n ≥ 2^k. -/
lemma le_of_bigOmega (n : ℕ) (k : ℕ) (hn : 2 ≤ n) (hk : bigOmega n = k) :
    2 ^ k ≤ n := hk ▸ pow_bigOmega_le n (by omega)

/-- 2^k itself is a k-almost-prime: Ω(2^k) = k. Combined with `le_of_bigOmega`,
    this shows 2^k is exactly the smallest k-almost-prime. -/
lemma bigOmega_two_pow (k : ℕ) : bigOmega (2 ^ k) = k := by
  unfold bigOmega
  rw [Nat.factorization_pow, Nat.Prime.factorization (p := 2) (by norm_num)]
  simp

/-- Ω is completely additive: Ω(a*b) = Ω(a) + Ω(b) for a, b ≠ 0. -/
lemma bigOmega_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  unfold bigOmega
  rw [Nat.factorization_mul ha hb]
  rw [Finsupp.sum_add_index' (by simp) (by simp)]

/-- Ω(1) = 0. -/
lemma bigOmega_one : bigOmega 1 = 0 := by
  unfold bigOmega
  simp

/-- Ω is monotone under strict divisor growth: if a ∣ n and a < n (a, n ≠ 0),
    then Ω(a) < Ω(n). -/
lemma bigOmega_lt_of_dvd_of_lt (a n : ℕ) (ha : a ≠ 0) (hn : n ≠ 0)
    (hdvd : a ∣ n) (hlt : a < n) : bigOmega a < bigOmega n := by
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at hc; omega
  have hc1 : c ≠ 1 := by
    rintro rfl; simp at hc; omega
  have hcO : 1 ≤ bigOmega c := by
    rcases Nat.eq_zero_or_pos (bigOmega c) with h0 | h0
    · exfalso
      apply hc1
      by_contra hc1'
      have hp := Nat.minFac_prime hc1'
      have hpdvd := Nat.minFac_dvd c
      obtain ⟨d, hd⟩ := hpdvd
      have hd0 : d ≠ 0 := by
        rintro rfl
        simp only [mul_zero] at hd
        exact hc0 hd
      have hp1 : bigOmega (Nat.minFac c) = 1 := by
        unfold bigOmega
        rw [hp.factorization]
        simp
      have := bigOmega_mul (Nat.minFac c) d hp.pos.ne' hd0
      rw [← hd, hp1, h0] at this
      omega
    · exact h0
  rw [hc, bigOmega_mul a c ha hc0]
  omega

/-- The counting function for k-almost-primes up to x. -/
noncomputable def piK (k : ℕ) (x : ℝ) : ℕ :=
  (Finset.Icc 2 ⌊x⌋₊).filter (fun n => bigOmega n = k) |>.card

/-- DEEP FACT (Landau, elementary form; not yet formalized): the count of
    k-almost-primes up to x is O(x (log log x)^(k-1) / log x). Stated with
    an explicit witness constant C_k rather than raw big-O, since the O
    needs to be usable inside a partial-summation argument. This is the one
    piece of real analytic number theory in the whole formalization; every
    other lemma in this file is either algebra or follows from this one. -/
lemma piK_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      (piK k x : ℝ) ≤ C * x * (Real.log (Real.log x)) ^ (k - 1) / Real.log x := by
  sorry -- THE deep step: elementary induction on k via the identity
        -- π_k(x) = Σ_{p ≤ x^(1/k)} π_{k-1}(x/p) + (correction for p > x^(1/k)),
        -- Chebyshev-type bounds on Σ_p 1/p up to y (Mertens' second theorem),
        -- and induction on k. This is a genuine multi-day sub-project
        -- (see e.g. Tenenbaum, "Introduction to Analytic and Probabilistic
        -- Number Theory", II.6, for the classical elementary argument).

/-- Given the counting bound, convergence follows by partial summation
    (Abel summation against π_k, using log n → ∞ to kill the count's
    polynomial-in-log-log growth). Standard once piK_bound is in hand. -/
lemma fk_summable (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n)) := by
  obtain ⟨C, hC, hbound⟩ := piK_bound k hk
  sorry -- partial summation against hbound; standard but not short.

def E (a₁ : ℝ) (k : ℕ) : ℝ := 2 ^ k * (1 - f k) - a₁ * k ^ 2

theorem criterion (a₁ : ℝ) (k : ℕ) :
    f (k + 1) - f k =
      (2 : ℝ) ^ (-(k : ℝ) - 1) *
        (a₁ * ((k : ℝ) ^ 2 - 2 * k - 1) + 2 * E a₁ k - E a₁ (k + 1)) := by
  have hrpow : (2 : ℝ) ^ (-(k : ℝ) - 1) = ((2 : ℝ) ^ (k + 1))⁻¹ := by
    rw [show (-(k : ℝ) - 1) = -(((k + 1 : ℕ) : ℝ)) by push_cast; ring]
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [hrpow]
  simp only [E]
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have h2' : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

lemma B_nonneg (j : ℕ) (u : ℝ) :
    0 ≤ (2 : ℝ) ^ (-(j : ℝ) * Real.exp (-u)) - 1 + j * Real.log 2 * Real.exp (-u) := by
  set x : ℝ := (j : ℝ) * Real.log 2 * Real.exp (-u) with hx
  have hx0 : 0 ≤ x := by positivity
  have h : (2 : ℝ) ^ (-(j : ℝ) * Real.exp (-u)) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1; rw [hx]; ring
  rw [h]
  have := Real.add_one_le_exp (-x)
  linarith

lemma geom_tail_bound (t : ℕ → ℝ) (n₀ : ℕ)
    (hratio : ∀ n ≥ n₀ + 1, |t (n + 1)| ≤ |t n| / 2)
    (hsum : Summable fun n => |t (n₀ + 1 + n)|) :
    |∑' n, t (n₀ + 1 + n)| ≤ 2 * |t (n₀ + 1)| := by
  have hbound : ∀ n : ℕ, |t (n₀ + 1 + n)| ≤ |t (n₀ + 1)| * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hr := hratio (n₀ + 1 + n) (by omega)
        have heq : n₀ + 1 + (n + 1) = (n₀ + 1 + n) + 1 := by omega
        rw [heq]
        calc |t (n₀ + 1 + n + 1)| ≤ |t (n₀ + 1 + n)| / 2 := hr
          _ ≤ (|t (n₀ + 1)| * (1 / 2) ^ n) / 2 := by linarith
          _ = |t (n₀ + 1)| * (1 / 2) ^ (n + 1) := by ring
  have hsummable_geom : Summable (fun n : ℕ => |t (n₀ + 1)| * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : ‖∑' n, t (n₀ + 1 + n)‖ ≤ ∑' n, ‖t (n₀ + 1 + n)‖ := norm_tsum_le_tsum_norm hsum
  have h2 : ∑' n, ‖t (n₀ + 1 + n)‖ ≤ ∑' n, |t (n₀ + 1)| * (1 / 2 : ℝ) ^ n := by
    apply Summable.tsum_le_tsum _ hsum hsummable_geom
    intro n
    simpa using hbound n
  have h3 : ∑' n, |t (n₀ + 1)| * (1 / 2 : ℝ) ^ n = |t (n₀ + 1)| * 2 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc |∑' n, t (n₀ + 1 + n)| = ‖∑' n, t (n₀ + 1 + n)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖t (n₀ + 1 + n)‖ := h1
    _ ≤ ∑' n, |t (n₀ + 1)| * (1 / 2 : ℝ) ^ n := h2
    _ = |t (n₀ + 1)| * 2 := h3
    _ = 2 * |t (n₀ + 1)| := by ring

noncomputable def dConst : ℝ := 0.3786950
noncomputable def rhoConst : ℝ := -0.1749323
noncomputable def SstarConst : ℝ := 6.9763
noncomputable def alphaConst : ℝ := 15.5716
noncomputable def GammaConst : ℝ := 105.41

structure NumericalFacts : Prop where
  d_enclosure   : |(0.3786950 : ℝ) - dConst| ≤ 5.3e-8
  rho_enclosure : |(-0.1749323 : ℝ) - rhoConst| ≤ 6.6e-8
  Sstar_bound   : SstarConst ≤ 6.9763
  alpha_bound   : alphaConst ≤ 15.5716
  Gamma_bound   : GammaConst ≤ 105.41

/-- The T_k tail bound denominator is positive for k ≥ 1. -/
lemma Tk_bound_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < (k : ℝ) * Real.log 2 * (2 ^ k - 1) := by
  have h1 : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0:ℝ) < (2:ℝ) ^ k - 1 := by
    have : (1:ℝ) < 2 ^ k := by
      calc (1:ℝ) < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
    linarith
  positivity

/-- The reciprocal tail bound decreases in k. -/
lemma Tk_bound_decreasing (k : ℕ) (hk : 1 ≤ k) :
    1 / (((k : ℝ) + 1) * Real.log 2 * (2 ^ (k + 1) - 1)) <
      1 / ((k : ℝ) * Real.log 2 * (2 ^ k - 1)) := by
  have hden_k : 0 < (k : ℝ) * Real.log 2 * (2 ^ k - 1) := Tk_bound_pos k hk
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hkge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have heq : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by ring
  have diff_eq :
      ((k : ℝ) + 1) * Real.log 2 * (2 ^ (k + 1) - 1) -
        (k : ℝ) * Real.log 2 * (2 ^ k - 1)
      = Real.log 2 * (((k : ℝ) + 2) * 2 ^ k - 1) := by
    rw [heq]; ring
  have bracket_pos : (0 : ℝ) < ((k : ℝ) + 2) * 2 ^ k - 1 := by
    nlinarith [hp2k, hkge1]
  have diff_pos :
      0 < ((k : ℝ) + 1) * Real.log 2 * (2 ^ (k + 1) - 1) -
        (k : ℝ) * Real.log 2 * (2 ^ k - 1) := by
    rw [diff_eq]; exact mul_pos hlog2 bracket_pos
  apply one_div_lt_one_div_of_lt hden_k
  linarith [diff_pos]

/-- The building block h(x) = exp(-x) - 1 + x is monotone increasing on
    [0, ∞). -/
lemma h_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - 1 + a ≤ Real.exp (-b) - 1 + b := by
  have hbase : Real.exp (-(b - a)) ≥ 1 - (b - a) := by
    have := Real.add_one_le_exp (-(b - a))
    linarith
  have hea_le1 : Real.exp (-a) ≤ 1 := by
    have hle : Real.exp (-a) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_zero] at hle
  have key : (b - a) ≥ Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    have h1 : (1 : ℝ) - Real.exp (-(b - a)) ≥ 0 := by
      have hle : Real.exp (-(b - a)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_zero] at hle
      linarith
    have step1 := mul_le_of_le_one_left h1 hea_le1
    linarith [step1, hbase]
  have hexp_split : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [key, hexp_split]

/-- B_j(u) is monotone increasing in j (real parameter ≥ 0), for fixed u.
    Behind the gap-5 domination B_{m-i} ≤ B_m. -/
lemma B_mono_in_param (u : ℝ) {j1 j2 : ℝ} (hj1 : 0 ≤ j1) (hj12 : j1 ≤ j2) :
    (2 : ℝ) ^ (-j1 * Real.exp (-u)) - 1 + j1 * Real.log 2 * Real.exp (-u) ≤
      (2 : ℝ) ^ (-j2 * Real.exp (-u)) - 1 + j2 * Real.log 2 * Real.exp (-u) := by
  have hrw : ∀ j : ℝ, (2 : ℝ) ^ (-j * Real.exp (-u)) =
      Real.exp (-(j * Real.log 2 * Real.exp (-u))) := by
    intro j
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1; ring
  rw [hrw j1, hrw j2]
  have heu : (0 : ℝ) ≤ Real.exp (-u) := (Real.exp_pos (-u)).le
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have ha : (0 : ℝ) ≤ j1 * Real.log 2 * Real.exp (-u) := by positivity
  have hab : j1 * Real.log 2 * Real.exp (-u) ≤ j2 * Real.log 2 * Real.exp (-u) := by
    apply mul_le_mul_of_nonneg_right _ heu
    exact mul_le_mul_of_nonneg_right hj12 hlog2
  exact h_mono ha hab

/-- Discrete corollary of B_mono_in_param: for natural j1 ≤ j2 (the actual
    index type used in the gap-5 sum Σ B_{m-i}), B is monotone. -/
lemma B_mono_nat (u : ℝ) {j1 j2 : ℕ} (hj12 : j1 ≤ j2) :
    (2 : ℝ) ^ (-(j1 : ℝ) * Real.exp (-u)) - 1 +
        (j1 : ℝ) * Real.log 2 * Real.exp (-u) ≤
      (2 : ℝ) ^ (-(j2 : ℝ) * Real.exp (-u)) - 1 +
        (j2 : ℝ) * Real.log 2 * Real.exp (-u) := by
  have hj1r : (0 : ℝ) ≤ (j1 : ℝ) := by positivity
  have hj12r : (j1 : ℝ) ≤ (j2 : ℝ) := by exact_mod_cast hj12
  exact B_mono_in_param u hj1r hj12r

/-- The gap-5 domination step: Σ_{i=0}^{m} B_{m-i}(u) ≤ (m+1)·B_m(u). -/
lemma B_sum_le (u : ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1),
        ((2 : ℝ) ^ (-((m - i : ℕ) : ℝ) * Real.exp (-u)) - 1 +
          ((m - i : ℕ) : ℝ) * Real.log 2 * Real.exp (-u))
      ≤ (m + 1) * ((2 : ℝ) ^ (-(m : ℝ) * Real.exp (-u)) - 1 +
          (m : ℝ) * Real.log 2 * Real.exp (-u)) := by
  calc ∑ i ∈ Finset.range (m + 1),
      ((2 : ℝ) ^ (-((m - i : ℕ) : ℝ) * Real.exp (-u)) - 1 +
        ((m - i : ℕ) : ℝ) * Real.log 2 * Real.exp (-u))
      ≤ ∑ _i ∈ Finset.range (m + 1),
          ((2 : ℝ) ^ (-(m : ℝ) * Real.exp (-u)) - 1 +
            (m : ℝ) * Real.log 2 * Real.exp (-u)) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact B_mono_nat u (Nat.sub_le m i)
    _ = (m + 1) * ((2 : ℝ) ^ (-(m : ℝ) * Real.exp (-u)) - 1 +
          (m : ℝ) * Real.log 2 * Real.exp (-u)) := by
        rw [Finset.sum_const, Finset.card_range]
        push_cast
        ring

/-- Σ_{i=0}^{m} (2u)^i/i! ≤ exp(2u) for u ≥ 0. -/
lemma sum_exp_terms_le (u : ℝ) (hu : 0 ≤ u) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (2 * u) ^ i / Nat.factorial i ≤ Real.exp (2 * u) := by
  have h2u : (0 : ℝ) ≤ 2 * u := by linarith
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummable : Summable (fun i => (2 * u) ^ i / Nat.factorial i) :=
    Real.summable_pow_div_factorial (2 * u)
  have hnn : ∀ i ∉ Finset.range (m + 1), (0:ℝ) ≤ (2 * u) ^ i / Nat.factorial i := by
    intro i _hi
    positivity
  first
  | exact sum_le_tsum (Finset.range (m + 1)) hnn hsummable
  | exact Finset.sum_le_tsum (Finset.range (m + 1)) hnn hsummable
  | exact hsummable.sum_le_tsum (Finset.range (m + 1)) hnn

/-- F_k(s) := Σ_{Ω(n)=k} n^{-s}, the Dirichlet series restricted to
    k-almost-primes. -/
noncomputable def Fk (k : ℕ) (s : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k}, (n : ℝ) ^ (-s)

/-- F_k(s) is summable for s > 1. -/
lemma Fk_summable (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} => (n : ℝ) ^ (-s)) := by
  have hcomp : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact hcomp.subtype _

/-- ∫₁^∞ n^{-s} ds = 1/(n log n) for n ≥ 2. -/
lemma integral_n_neg_s (n : ℕ) (hn : 2 ≤ n) :
    ∫ s in Set.Ioi (1:ℝ), (n:ℝ) ^ (-s) =
      1 / ((n : ℝ) * Real.log n) := by
  have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  have hpteq : ∀ s : ℝ, (n:ℝ) ^ (-s) = Real.exp (-(Real.log n * s)) := by
    intro s
    rw [Real.rpow_def_of_pos hnpos]
    congr 1; ring
  simp_rw [hpteq]
  rw [MeasureTheory.integral_comp_mul_left_Ioi (fun u => Real.exp (-u)) 1 hlogn]
  simp only [smul_eq_mul, mul_one]
  rw [integral_exp_neg_Ioi, Real.exp_neg, Real.exp_log hnpos]
  rw [one_div, mul_inv]
  ring

/-- The Tonelli exchange: f_k = ∫₁^∞ F_k(s) ds. -/
lemma fk_eq_integral_Fk (k : ℕ) (hk : 1 ≤ k)
    (hsum1 : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n))) :
    f k = ∫ s in Set.Ioi (1:ℝ), Fk k s := by
  unfold f Fk
  have habs : ∀ (n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k}) (s : ℝ),
      ‖(n:ℝ) ^ (-s)‖ = (n:ℝ) ^ (-s) := by
    intro n s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm_eq : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      ∫ s in Set.Ioi (1:ℝ), ‖(n:ℝ) ^ (-s)‖ = 1 / ((n:ℝ) * Real.log n) := by
    intro n
    simp_rw [habs]
    exact integral_n_neg_s n n.2.1
  have hsummable_norm : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      ∫ s in Set.Ioi (1:ℝ), ‖(n:ℝ) ^ (-s)‖) := by
    simp_rw [hnorm_eq]; exact hsum1
  have hint : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      MeasureTheory.Integrable (fun s => (n:ℝ) ^ (-s))
        (MeasureTheory.volume.restrict (Set.Ioi (1:ℝ))) := by
    intro n
    by_contra hni
    have hz := MeasureTheory.integral_undef hni
    rw [integral_n_neg_s n n.2.1] at hz
    have : (0:ℝ) < 1 / ((n:ℝ) * Real.log n) := by
      have hn2 : 2 ≤ (n:ℕ) := n.2.1
      have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < (n:ℕ))
      have := Real.log_pos this
      positivity
    linarith [hz ▸ this]
  rw [tsum_congr (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} => (integral_n_neg_s n n.2.1).symm)]
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable_norm

/-- The function s ↦ n^{-s} is continuous. -/
lemma continuous_n_neg_s (n : ℕ) (hn : 2 ≤ n) : Continuous (fun s : ℝ => (n:ℝ) ^ (-s)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  exact (Real.continuous_const_rpow hnpos.ne').comp continuous_neg

/-- n^{-s} is integrable on Ioi 1. -/
lemma integrable_n_neg_s_Ioi1 (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.Integrable (fun s : ℝ => (n:ℝ) ^ (-s))
      (MeasureTheory.volume.restrict (Set.Ioi (1:ℝ))) := by
  by_contra hni
  have hz := MeasureTheory.integral_undef hni
  rw [integral_n_neg_s n hn] at hz
  have : (0:ℝ) < 1 / ((n:ℝ) * Real.log n) := by
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    have := Real.log_pos hn1
    positivity
  linarith [hz ▸ this]

/-- n^{-s} is integrable on Ioi 2 (via Ioi 2 ⊆ Ioi 1). -/
lemma integrable_n_neg_s_Ioi2 (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.Integrable (fun s : ℝ => (n:ℝ) ^ (-s))
      (MeasureTheory.volume.restrict (Set.Ioi (2:ℝ))) := by
  have hsub : Set.Ioi (2:ℝ) ⊆ Set.Ioi (1:ℝ) := fun x hx => lt_trans (by norm_num : (1:ℝ) < 2) hx
  exact MeasureTheory.IntegrableOn.mono_set (integrable_n_neg_s_Ioi1 n hn) hsub

/-- Splitting the improper integral at s=2. -/
lemma integral_n_neg_s_split (n : ℕ) (hn : 2 ≤ n) :
    ∫ s in Set.Ioi (1:ℝ), (n:ℝ) ^ (-s) ∂MeasureTheory.volume =
      ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume +
        ∫ s in Set.Ioi (2:ℝ), (n:ℝ) ^ (-s) ∂MeasureTheory.volume := by
  have hunion : Set.Ioi (1:ℝ) = Set.Ioc (1:ℝ) 2 ∪ Set.Ioi (2:ℝ) := by
    rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  have hdisj : Disjoint (Set.Ioc (1:ℝ) 2) (Set.Ioi (2:ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx2⟩ hx2'
    exact absurd hx2 (not_le.mpr hx2')
  rw [hunion]
  exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    ((continuous_n_neg_s n hn).integrableOn_Ioc)
    (integrable_n_neg_s_Ioi2 n hn)

/-- ∫₂^∞ n^{-s} ds = 1/(n² log n) for n ≥ 2. -/
lemma integral_n_neg_s_Ioi2_value (n : ℕ) (hn : 2 ≤ n) :
    ∫ s in Set.Ioi (2:ℝ), (n:ℝ) ^ (-s) ∂MeasureTheory.volume =
      1 / ((n:ℝ) ^ 2 * Real.log n) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hpteq : ∀ s : ℝ, (n:ℝ) ^ (-s) = Real.exp (-(Real.log n * s)) := by
    intro s
    rw [Real.rpow_def_of_pos hnpos]
    congr 1; ring
  simp_rw [hpteq]
  rw [MeasureTheory.integral_comp_mul_left_Ioi (fun u => Real.exp (-u)) 2 hlogn]
  simp only [smul_eq_mul]
  rw [integral_exp_neg_Ioi, Real.exp_neg]
  have hexp2 : Real.exp (Real.log n * 2) = (n:ℝ) ^ 2 := by
    have heq : Real.log (n:ℝ) * 2 = Real.log n + Real.log n := by ring
    rw [heq, Real.exp_add, Real.exp_log hnpos]
    ring
  rw [hexp2]
  rw [one_div, mul_inv]
  ring

/-- I_k := ∫₁² F_k(s) ds. -/
noncomputable def Ik (k : ℕ) : ℝ := ∫ s in Set.Ioc (1:ℝ) 2, Fk k s ∂MeasureTheory.volume

/-- T_k := Σ_{Ω(n)=k} 1/(n² log n). -/
noncomputable def Tk (k : ℕ) : ℝ :=
  ∑' n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k}, 1 / ((n : ℝ) ^ 2 * Real.log n)

/-- LEMMA 1 (foundation): f_k = I_k + T_k. -/
theorem lemma1_foundation (k : ℕ) (hk : 1 ≤ k)
    (hsum1 : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n))) :
    f k = Ik k + Tk k := by
  have hn2 : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k}, 2 ≤ (n : ℕ) := fun n => n.2.1
  have hIoc_le : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      0 ≤ ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume ∧
      ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume
        ≤ 1 / ((n:ℝ) * Real.log n) := by
    intro n
    have hsplit := integral_n_neg_s_split n (hn2 n)
    have hpt := integral_n_neg_s n (hn2 n)
    have hIoi2nonneg : 0 ≤ ∫ s in Set.Ioi (2:ℝ), (n:ℝ) ^ (-s) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_nonneg; intro s; positivity
    have hIocnonneg : 0 ≤ ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_nonneg; intro s; positivity
    refine ⟨hIocnonneg, ?_⟩
    rw [← hpt]
    linarith [hsplit, hIoi2nonneg]
  have hsummable_Ioc : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume) :=
    Summable.of_nonneg_of_le (fun n => (hIoc_le n).1) (fun n => (hIoc_le n).2) hsum1
  have hTk_le : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      0 ≤ 1 / ((n:ℝ) ^ 2 * Real.log n) ∧
        1 / ((n:ℝ) ^ 2 * Real.log n) ≤ 1 / ((n:ℝ) * Real.log n) := by
    intro n
    have hnpos : (0:ℝ) < (n:ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) (hn2 n))
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < (n:ℕ))
    have hlogn := Real.log_pos hn1
    have hnpos2 : (0:ℝ) < (n:ℝ) ^ 2 := pow_pos hnpos 2
    have hprod : 0 < (n:ℝ) ^ 2 * Real.log n := mul_pos hnpos2 hlogn
    have hprod1 : 0 < (n:ℝ) * Real.log n := mul_pos hnpos hlogn
    constructor
    · exact le_of_lt (div_pos (by norm_num) hprod)
    · apply div_le_div_of_nonneg_left (by norm_num) hprod1
      nlinarith [sq_nonneg ((n:ℝ) - 1)]
  have hsummable_Tk : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n:ℝ) ^ 2 * Real.log n)) :=
    Summable.of_nonneg_of_le (fun n => (hTk_le n).1) (fun n => (hTk_le n).2) hsum1
  unfold f
  rw [tsum_congr (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
    (integral_n_neg_s n (hn2 n)).symm)]
  have hpt_split2 : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      ∫ s in Set.Ioi (1:ℝ), (n:ℝ) ^ (-s) ∂MeasureTheory.volume =
        ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume +
          1 / ((n:ℝ) ^ 2 * Real.log n) := by
    intro n
    rw [integral_n_neg_s_split n (hn2 n), integral_n_neg_s_Ioi2_value n (hn2 n)]
  rw [tsum_congr hpt_split2, Summable.tsum_add hsummable_Ioc hsummable_Tk]
  congr 1
  · have hint : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
        MeasureTheory.Integrable (fun s : ℝ => (n:ℝ) ^ (-s))
          (MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) 2)) :=
      fun n => (continuous_n_neg_s n (hn2 n)).integrableOn_Ioc
    unfold Ik Fk
    have hnorm_eq : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
        ∫ s in Set.Ioc (1:ℝ) 2, ‖(n:ℝ) ^ (-s)‖ ∂MeasureTheory.volume =
          ∫ s in Set.Ioc (1:ℝ) 2, (n:ℝ) ^ (-s) ∂MeasureTheory.volume := by
      intro n
      congr 1
      funext s
      exact Real.norm_of_nonneg (by positivity)
    have hsummable_norm2 : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
        ∫ s in Set.Ioc (1:ℝ) 2, ‖(n:ℝ) ^ (-s)‖ ∂MeasureTheory.volume) :=
      hsummable_Ioc.congr (fun n => (hnorm_eq n).symm)
    exact MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable_norm2

/-- LINK 3 (assembly), pure algebra given the coefficient sums as data. -/
theorem assembly_identity (k : ℕ) (c δ : ℕ → ℝ) (q : ℝ) :
    ∑ i ∈ Finset.range (k + 1), c i * 2 ^ i * (2 ^ (k - i + 1) - q * ((k - i : ℕ):ℝ) ^ 2 + δ (k - i)) =
      2 ^ (k + 1) * (∑ i ∈ Finset.range (k + 1), c i) -
        q * ((k:ℝ) ^ 2 * (∑ i ∈ Finset.range (k + 1), 2 ^ i * c i) -
          2 * k * (∑ i ∈ Finset.range (k + 1), (i:ℝ) * 2 ^ i * c i) +
          (∑ i ∈ Finset.range (k + 1), (i:ℝ) ^ 2 * 2 ^ i * c i)) +
        (∑ i ∈ Finset.range (k + 1), 2 ^ i * c i * δ (k - i)) := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      c i * 2 ^ i * (2 ^ (k - i + 1) - q * ((k - i : ℕ):ℝ) ^ 2 + δ (k - i)) =
        c i * 2 ^ (k + 1) -
          q * (c i * 2 ^ i * (k:ℝ) ^ 2 - 2 * k * (c i * 2 ^ i * (i:ℝ)) + c i * 2 ^ i * (i:ℝ) ^ 2) +
          c i * 2 ^ i * δ (k - i) := by
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi; omega
    have hcast : ((k - i : ℕ):ℝ) = (k:ℝ) - (i:ℝ) := Nat.cast_sub hik
    have hexp : (2:ℝ) ^ i * 2 ^ (k - i + 1) = 2 ^ (k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hcast]
    have expand :
        c i * 2 ^ i * ((2:ℝ) ^ (k - i + 1) - q * ((k:ℝ) - i) ^ 2 + δ (k - i)) =
          c i * (2 ^ i * 2 ^ (k - i + 1)) -
            q * (c i * 2 ^ i * ((k:ℝ) - i) ^ 2) + c i * 2 ^ i * δ (k - i) := by
      ring
    rw [expand, hexp]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- Lemma 1 substituted into E(k)'s actual definition. -/
theorem E_eq_via_lemma1 (a₁ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hsum1 : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n))) :
    E a₁ k = 2 ^ k * (1 - Ik k - Tk k) - a₁ * k ^ 2 := by
  unfold E
  rw [lemma1_foundation k hk hsum1]
  ring

/-- Fully explicit criterion: f(k+1)-f(k) purely in terms of I_k,T_k. -/
theorem criterion_explicit (a₁ : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hsum1 : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n)))
    (hsum1' : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = (k+1)} =>
      1 / ((n : ℝ) * Real.log n))) :
    f (k + 1) - f k =
      (2 : ℝ) ^ (-(k : ℝ) - 1) *
        (a₁ * ((k : ℝ) ^ 2 - 2 * k - 1) +
          2 * (2 ^ k * (1 - Ik k - Tk k) - a₁ * k ^ 2) -
          (2 ^ (k+1) * (1 - Ik (k+1) - Tk (k+1)) - a₁ * (k+1:ℝ) ^ 2)) := by
  rw [criterion a₁ k, E_eq_via_lemma1 a₁ k hk hsum1, E_eq_via_lemma1 a₁ (k+1) (by omega) hsum1']
  push_cast
  ring

/-- T_k ≥ 0. -/
theorem Tk_nonneg (k : ℕ) : 0 ≤ Tk k := by
  unfold Tk
  apply tsum_nonneg
  intro n
  positivity

/-- log(1-x)+x ≤ 0 for x ∈ [0,1). -/
theorem log_one_sub_add_self_nonpos (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) + x ≤ 0 := by
  have hderiv : ∀ y ∈ Set.Ico (0:ℝ) 1, HasDerivAt (fun t => Real.log (1 - t) + t)
      (-1 / (1 - y) + 1) y := by
    intro y hy
    have hy1 : (1:ℝ) - y ≠ 0 := by
      have := hy.2; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - y)) y := by
      have := h1.log hy1
      simpa using this
    exact h2.add (hasDerivAt_id y)
  have hanti : AntitoneOn (fun t => Real.log (1 - t) + t) (Set.Ico (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
    · apply ContinuousOn.add
      · apply ContinuousOn.log (by fun_prop)
        intro y hy
        have := hy.2; linarith [hy.2]
      · fun_prop
    · intro y hy
      rw [interior_Ico] at hy
      exact ((hderiv y (Set.mem_Ico.mpr ⟨hy.1.le, hy.2⟩)).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      have hd := hderiv y (Set.mem_Ico.mpr ⟨hy.1.le, hy.2⟩)
      rw [hd.deriv]
      have hy1 : (0:ℝ) < 1 - y := by linarith [hy.2]
      have hyy : (0:ℝ) ≤ y := hy.1.le
      have heq : -1 / (1 - y) + 1 = -y / (1 - y) := by field_simp; ring
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hy1.le
  have h0 := hanti (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) (Set.mem_Ico.mpr ⟨hx0, hx1⟩) hx0
  simpa using h0

/-- log(1-x)+x ≥ -x²/(1-x) for x ∈ [0,1). -/
theorem log_one_sub_add_self_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -(x^2 / (1 - x)) ≤ Real.log (1 - x) + x := by
  have hderiv : ∀ y ∈ Set.Ico (0:ℝ) 1,
      HasDerivAt (fun t => Real.log (1 - t) + t + t^2 / (1 - t))
        (-1 / (1 - y) + 1 + (2 * y * (1 - y) - y^2 * (-1)) / (1 - y)^2) y := by
    intro y hy
    have hy1 : (1:ℝ) - y ≠ 0 := by
      have := hy.2; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - y)) y := by
      have := h1.log hy1
      simpa using this
    have h3 : HasDerivAt (fun t : ℝ => t^2) (2 * y) y := by
      have := hasDerivAt_pow 2 y
      simpa using this
    have h4 : HasDerivAt (fun t : ℝ => t^2 / (1 - t))
        ((2 * y * (1 - y) - y^2 * (-1)) / (1 - y)^2) y := h3.div h1 hy1
    exact (h2.add (hasDerivAt_id y)).add h4
  have hmono : MonotoneOn (fun t => Real.log (1 - t) + t + t^2 / (1 - t)) (Set.Ico (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · apply ContinuousOn.add
      · apply ContinuousOn.add
        · apply ContinuousOn.log (by fun_prop)
          intro y hy; have := hy.2; linarith [hy.2]
        · fun_prop
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro y hy; have := hy.2; simp; linarith [hy.2]
    · intro y hy
      rw [interior_Ico] at hy
      exact ((hderiv y (Set.mem_Ico.mpr ⟨hy.1.le, hy.2⟩)).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      have hd := hderiv y (Set.mem_Ico.mpr ⟨hy.1.le, hy.2⟩)
      rw [hd.deriv]
      have hy1 : (0:ℝ) < 1 - y := by linarith [hy.2]
      have hyy : (0:ℝ) ≤ y := hy.1.le
      have heq : -1 / (1 - y) + 1 + (2 * y * (1 - y) - y^2 * (-1)) / (1 - y)^2 = y / (1 - y)^2 := by
        field_simp; ring
      rw [heq]
      positivity
  have h0 := hmono (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) (Set.mem_Ico.mpr ⟨hx0, hx1⟩) hx0
  simp only [Real.log_one, sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_div, add_zero, zero_add] at h0
  linarith

/-- log(1+y)-y ≤ 0 for y ≥ 0. -/
theorem log_one_add_sub_self_nonpos (y : ℝ) (hy0 : 0 ≤ y) :
    Real.log (1 + y) - y ≤ 0 := by
  have hderiv : ∀ t ∈ Set.Ici (0:ℝ), HasDerivAt (fun s => Real.log (1 + s) + -s)
      (1 / (1 + t) + -1) t := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := ht
    have ht1 : (1:ℝ) + t ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1:ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      have := h1.log ht1
      simpa using this
    have h3 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    exact h2.add h3
  have hanti : AntitoneOn (fun s => Real.log (1 + s) + -s) (Set.Ici (0:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · apply ContinuousOn.add
      · apply ContinuousOn.log (by fun_prop)
        intro t ht
        have ht0 : (0:ℝ) ≤ t := ht
        positivity
      · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hderiv t (Set.mem_Ici.mpr ht.le)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0:ℝ) < t := ht
      have hd := hderiv t (Set.mem_Ici.mpr ht0.le)
      rw [hd.deriv]
      have ht1 : (0:ℝ) < 1 + t := by linarith
      have : (1:ℝ) / (1 + t) ≤ 1 := by
        rw [div_le_one ht1]; linarith
      linarith
  have h0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy0) hy0
  simp only [Real.log_one, add_zero] at h0
  linarith

/-- log(1+y)-y ≥ -y²/2 for y ≥ 0. -/
theorem log_one_add_sub_self_lower (y : ℝ) (hy0 : 0 ≤ y) :
    -(y^2 / 2) ≤ Real.log (1 + y) - y := by
  have hderiv : ∀ t ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun s => Real.log (1 + s) + -s + s^2 / 2)
        (1 / (1 + t) + -1 + t) t := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := ht
    have ht1 : (1:ℝ) + t ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1:ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      have := h1.log ht1
      simpa using this
    have h3neg : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    have h4 : HasDerivAt (fun s : ℝ => s^2 / 2) t t := by
      have := (hasDerivAt_pow 2 t).div_const 2
      simpa using this
    exact (h2.add h3neg).add h4
  have hmono : MonotoneOn (fun s => Real.log (1 + s) + -s + s^2 / 2) (Set.Ici (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · apply ContinuousOn.add
      · apply ContinuousOn.add
        · apply ContinuousOn.log (by fun_prop)
          intro t ht
          have ht0 : (0:ℝ) ≤ t := ht
          positivity
        · fun_prop
      · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hderiv t (Set.mem_Ici.mpr ht.le)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0:ℝ) < t := ht
      have hd := hderiv t (Set.mem_Ici.mpr ht0.le)
      rw [hd.deriv]
      have ht1 : (0:ℝ) < 1 + t := by linarith
      have hkey : 1 / (1 + t) + -1 + t = t^2 / (1 + t) := by
        field_simp; ring
      rw [hkey]; positivity
  have h0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy0) hy0
  simp only [add_zero, Real.log_one] at h0
  linarith

/-- Combined two-sided log bound: |log(1-x)+x| ≤ 3x² for |x| ≤ 2/3. -/
theorem log_bound_combined (x : ℝ) (hx : |x| ≤ 2/3) :
    |Real.log (1 - x) + x| ≤ 3 * x^2 := by
  by_cases hx0 : (0:ℝ) ≤ x
  · have hx1 : x < 1 := by
      have := abs_le.mp hx; linarith [this.2]
    have hub := log_one_sub_add_self_nonpos x hx0 hx1
    have hlb := log_one_sub_add_self_lower x hx0 hx1
    have hxle : x ≤ 2/3 := (abs_le.mp hx).2
    have h1mx : (1:ℝ)/3 ≤ 1 - x := by linarith
    rw [abs_le]
    constructor
    · have : x^2 / (1 - x) ≤ 3 * x^2 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - x)]
        nlinarith [sq_nonneg x]
      linarith
    · nlinarith [hub, sq_nonneg x]
  · set y := -x with hy
    have hy0 : 0 ≤ y := by linarith
    have hub := log_one_add_sub_self_nonpos y hy0
    have hlb := log_one_add_sub_self_lower y hy0
    have hxy : Real.log (1 - x) + x = Real.log (1 + y) - y := by rw [hy]; ring_nf
    rw [hxy, abs_le]
    have hy2 : y^2 = x^2 := by rw [hy]; ring
    constructor
    · linarith [hlb, hy2.symm ▸ hlb]
    · nlinarith [hub, hy2]

/-- The per-prime log-correction bound: for p ≥ 3, s ≥ 1, |z| ≤ 2,
    |{-log(1-z p^{-s})} + z log(1-p^{-s})| ≤ 18 p^{-2s}. -/
theorem prime_correction_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))|
      ≤ 18 * (p:ℝ) ^ (-2*s) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hza_le : |z * a| ≤ 2/3 := by
    rw [abs_mul, abs_of_pos ha_pos]
    have hmm : |z| * a ≤ 2 * (1/3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have ha_le2 : |a| ≤ 2/3 := by rw [abs_of_pos ha_pos]; linarith
  have hr1 := log_bound_combined (z * a) hza_le
  have hr2 := log_bound_combined a ha_le2
  have hkey : (-Real.log (1 - z * a)) + z * Real.log (1 - a)
      = -(Real.log (1 - z * a) + z * a) + z * (Real.log (1 - a) + a) := by ring
  rw [hkey]
  have hstep1 : |(-(Real.log (1 - z * a) + z * a) + z * (Real.log (1 - a) + a))|
      ≤ |Real.log (1 - z * a) + z * a| + |z * (Real.log (1 - a) + a)| := by
    have habs : |(-(Real.log (1 - z * a) + z * a)) + z * (Real.log (1 - a) + a)|
        ≤ |(-(Real.log (1 - z * a) + z * a))| + |z * (Real.log (1 - a) + a)| := by
      first
      | exact abs_add _ _
      | exact abs_add_le _ _
      | exact abs_add (-(Real.log (1 - z * a) + z * a)) (z * (Real.log (1 - a) + a))
    rwa [abs_neg] at habs
  have hstep2 : |z * (Real.log (1 - a) + a)| ≤ |z| * (3 * a^2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hr2 (abs_nonneg z)
  have hfinal : |Real.log (1 - z * a) + z * a| + |z * (Real.log (1 - a) + a)|
      ≤ 3 * (z*a)^2 + |z| * (3 * a^2) := by linarith
  have hbound : 3 * (z*a)^2 + |z| * (3 * a^2) ≤ 18 * a^2 := by
    have hz2 : z^2 ≤ 4 := by nlinarith [abs_le.mp hz]
    nlinarith [sq_nonneg a, hz2, hz, sq_abs z]
  have heq : (18:ℝ) * a^2 = 18 * (p:ℝ) ^ (-2*s) := by
    rw [ha_def, ← Real.rpow_natCast ((p:ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
    ring_nf
  calc |(-(Real.log (1 - z * a) + z * a) + z * (Real.log (1 - a) + a))|
      ≤ |Real.log (1 - z * a) + z * a| + |z * (Real.log (1 - a) + a)| := hstep1
    _ ≤ 3 * (z*a)^2 + |z| * (3 * a^2) := hfinal
    _ ≤ 18 * a^2 := hbound
    _ = 18 * (p:ℝ) ^ (-2*s) := heq

/-- Summability of the per-prime correction terms. -/
theorem prime_correction_summable (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      |(-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))|) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => 18 * (p:ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (18:ℝ) * (p:ℝ) ^ (-2*s) =
        18 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => abs_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => prime_correction_bound (p:ℕ) p.property.2 s hs z hz)
    hcomp

/-- |exp(x)-1| ≤ 2|x| for |x| ≤ 1. -/
theorem abs_exp_sub_one_le (x : ℝ) (hx : |x| ≤ 1) : |Real.exp x - 1| ≤ 2 * |x| := by
  by_cases hx0 : x ≤ 0
  · have hlb : (1:ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hub : Real.exp x ≤ 1 := by
      have := Real.exp_le_exp.mpr hx0
      simpa using this
    rw [abs_of_nonpos (by linarith : Real.exp x - 1 ≤ 0)]
    rw [abs_of_nonpos hx0]
    linarith
  · push_neg at hx0
    have hx1 : x ≤ 1 := by
      have := abs_le.mp hx; linarith [this.2]
    have hlog2mem : Real.log 2 ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨Real.log_nonneg (by norm_num), ?_⟩
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have he3 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hderiv : ∀ t : ℝ, HasDerivAt (fun u => 1 + 2*u + -Real.exp u) (2 + -Real.exp t) t := by
      intro t
      have h1 : HasDerivAt (fun u : ℝ => 1 + 2*u) 2 t := by
        simpa using ((hasDerivAt_id t).const_mul 2).const_add (1:ℝ)
      have h2 : HasDerivAt (fun u : ℝ => -Real.exp u) (-Real.exp t) t :=
        (Real.hasDerivAt_exp t).neg
      exact h1.add h2
    have hub : Real.exp x ≤ 1 + 2 * x := by
      by_cases hcase : x ≤ Real.log 2
      · have hmono : MonotoneOn (fun u => 1 + 2*u + -Real.exp u) (Set.Icc 0 (Real.log 2)) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.log 2))
          · fun_prop
          · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [interior_Icc] at ht
            rw [(hderiv t).deriv]
            have : Real.exp t ≤ 2 := by
              rw [show (2:ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
              exact Real.exp_le_exp.mpr ht.2.le
            linarith
        have h0 := hmono (Set.mem_Icc.mpr ⟨le_refl 0, hlog2mem.1⟩)
          (Set.mem_Icc.mpr ⟨hx0.le, hcase⟩) hx0.le
        simp only [mul_zero, add_zero, Real.exp_zero] at h0
        linarith
      · push_neg at hcase
        have hmono : AntitoneOn (fun u => 1 + 2*u + -Real.exp u) (Set.Icc (Real.log 2) 1) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc (Real.log 2) 1)
          · fun_prop
          · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [interior_Icc] at ht
            rw [(hderiv t).deriv]
            have : (2:ℝ) ≤ Real.exp t := by
              rw [show (2:ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
              exact Real.exp_le_exp.mpr ht.1.le
            linarith
        have h0 := hmono (Set.mem_Icc.mpr ⟨hcase.le, hx1⟩)
          (Set.mem_Icc.mpr ⟨hlog2mem.2, le_refl 1⟩) hx1
        simp only at h0
        nlinarith [h0, he3]
    have hlb : (1:ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp x - 1)]
    rw [abs_of_pos hx0]
    linarith

/-- For p ≥ 5, s ≥ 1: 18p^{-2s} ≤ 1. p=3 handled separately later
    as an ordinary finite factor, not through Multipliable machinery. -/
theorem correction_le_one (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    18 * (p:ℝ) ^ (-2*s) ≤ 1 := by
  have hp5 : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hpos : (0:ℝ) < (p:ℝ) := by linarith
  have h1 : (p:ℝ) ^ (-2*s) ≤ (p:ℝ) ^ (-2:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpow : (5:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2:ℝ) :=
    Real.rpow_le_rpow (by norm_num) hp5 (by norm_num)
  have heq5 : (5:ℝ) ^ (-2:ℝ) = ((5:ℝ) ^ (2:ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) 2
  have heqp : (p:ℝ) ^ (-2:ℝ) = ((p:ℝ) ^ (2:ℝ))⁻¹ :=
    Real.rpow_neg hpos.le 2
  have h2 : (p:ℝ) ^ (-2:ℝ) ≤ (5:ℝ) ^ (-2:ℝ) := by
    rw [heqp, heq5]
    gcongr
  have h5val : (5:ℝ) ^ (-2:ℝ) = 1/25 := by
    rw [heq5]
    norm_num [Real.rpow_natCast]
  have hchain : (p:ℝ) ^ (-2*s) ≤ 1/25 := le_trans h1 (h2.trans_eq h5val)
  linarith [hchain]

/-- |exp(correction_p) - 1| ≤ 36 p^{-2s} for p ≥ 5. -/
theorem prime_factor_sub_one_bound (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |Real.exp ((-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))) - 1|
      ≤ 36 * (p:ℝ) ^ (-2*s) := by
  set c : ℝ := (-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))
    with hc_def
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by
    have : (5:ℕ) ≤ p := hp
    have : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast this
    linarith
  have hp3nat : 3 ≤ p := by omega
  have hbound : |c| ≤ 18 * (p:ℝ) ^ (-2*s) := prime_correction_bound p hp3nat s hs z hz
  have hle1 : 18 * (p:ℝ) ^ (-2*s) ≤ 1 := correction_le_one p hp s hs
  have hc1 : |c| ≤ 1 := le_trans hbound hle1
  have hexp := abs_exp_sub_one_le c hc1
  calc |Real.exp c - 1| ≤ 2 * |c| := hexp
    _ ≤ 2 * (18 * (p:ℝ) ^ (-2*s)) := by linarith
    _ = 36 * (p:ℝ) ^ (-2*s) := by ring

/-- Summability of |factor_p - 1| over primes p ≥ 5. -/
theorem prime_factor_sub_one_summable (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      |Real.exp ((-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))) - 1|) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 36 * (p:ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (36:ℝ) * (p:ℝ) ^ (-2*s) =
        36 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 36
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => abs_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => prime_factor_sub_one_bound (p:ℕ) p.property.2 s hs z hz)
    hcomp

/-- The G₂ per-prime factor equals exp(correction_p). -/
theorem prime_factor_eq_exp (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    (1 - z * (p:ℝ) ^ (-s))⁻¹ * (1 - (p:ℝ) ^ (-s)) ^ z =
      Real.exp ((-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hza_lt : z * a < 1 := by
    have : |z * a| ≤ 2/3 := by
      rw [abs_mul, abs_of_pos ha_pos]
      have hmm : |z| * a ≤ 2 * (1/3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
      linarith
    have := (abs_le.mp this).2
    linarith
  have h1za_pos : 0 < 1 - z * a := by linarith
  have h1a_pos : 0 < 1 - a := by linarith
  have hrpow_pos : 0 < (1 - a) ^ z := Real.rpow_pos_of_pos h1a_pos z
  have hfactor_pos : 0 < (1 - z * a)⁻¹ * (1 - a) ^ z := by positivity
  rw [← Real.exp_log hfactor_pos]
  congr 1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_inv,
    Real.log_rpow h1a_pos]

/-- MULTIPLIABLE: the G₂ per-prime factor is Multipliable over primes p≥5. -/
theorem prime_factor_multipliable (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (p:ℝ) ^ (-s))⁻¹ * (1 - (p:ℝ) ^ (-s)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + (Real.exp ((-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
    | exact multipliable_one_add_of_summable (f := fun p => Real.exp ((-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))) - 1) hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - z * (p:ℝ) ^ (-s))⁻¹ * (1 - (p:ℝ) ^ (-s)) ^ z =
        1 + (Real.exp ((-Real.log (1 - z * (p:ℝ) ^ (-s))) + z * Real.log (1 - (p:ℝ) ^ (-s))) - 1) := by
    intro p
    have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
    rw [prime_factor_eq_exp (p:ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult

/-- The tail of G₂: infinite product over primes p≥5. -/
noncomputable def G2tail (s z : ℝ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (1 - z * (p:ℝ) ^ (-s))⁻¹ * (1 - (p:ℝ) ^ (-s)) ^ z

/-- G2tail actually has this product as its value, since the family is
    genuinely Multipliable. -/
theorem G2tail_hasProd (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (p:ℝ) ^ (-s))⁻¹ * (1 - (p:ℝ) ^ (-s)) ^ z) (G2tail s z) :=
  (prime_factor_multipliable s hs z hz).hasProd

/-- The full G₂(s,z): p=3 factor times the convergent tail over p≥5. -/
noncomputable def G2 (s z : ℝ) : ℝ :=
  (1 - z * (3:ℝ) ^ (-s))⁻¹ * (1 - (3:ℝ) ^ (-s)) ^ z * G2tail s z

/-- Complex log bound: |log(1-w)+w| ≤ |w|²/(1-|w|) for |w|<1. -/
theorem complex_log_bound (w : ℂ) (hw : ‖w‖ < 1) :
    ‖Complex.log (1 - w) + w‖ ≤ ‖w‖^2 / (1 - ‖w‖) := by
  have hre_le_norm : ∀ v : ℂ, |v.re| ≤ ‖v‖ := by
    intro v
    have hns : v.re^2 ≤ Complex.normSq v := by
      have : Complex.normSq v = v.re^2 + v.im^2 := by
        rw [Complex.normSq_apply]; ring
      nlinarith [sq_nonneg v.im, this]
    have hnormsq : ‖v‖^2 = Complex.normSq v := by
      first
      | rw [Complex.norm_eq_abs, Complex.abs_apply, Real.sq_sqrt (Complex.normSq_nonneg v)]
      | rw [Complex.sq_norm]
      | rw [Complex.norm_sq_apply]
      | exact (Complex.normSq_eq_abs v).symm ▸ (Complex.sq_abs v)
      | rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg v)]
    have : v.re^2 ≤ ‖v‖^2 := by rw [hnormsq]; exact hns
    nlinarith [abs_nonneg v.re, norm_nonneg v, sq_abs v.re, this]
  have hslit : ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - (t:ℂ) * w) ∈ Complex.slitPlane := by
    intro t ht
    have hre : (0:ℝ) < (1 - (t:ℂ) * w).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      have h1 : t ≤ 1 := ht.2
      have h2 : (0:ℝ) ≤ t := ht.1
      have h3 : t * w.re ≤ ‖w‖ := by
        have h4 := hre_le_norm w
        rw [abs_le] at h4
        nlinarith [h4.2]
      nlinarith [hw, h3]
    left; exact hre
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => -Complex.log (1 - (s:ℂ) * w)) (w / (1 - (t:ℂ) * w)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (1:ℂ) - (s:ℂ) * w) (-w) t := by
      have hid : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) t := by
        first
        | exact Complex.hasDerivAt_ofReal t
        | simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
        | exact (hasDerivAt_id t).ofReal_comp
      simpa using (hid.mul_const w).const_sub (1:ℂ)
    have hslit_t := hslit t ht
    have hlogderiv : HasDerivAt Complex.log (1 - (t:ℂ) * w)⁻¹ (1 - (t:ℂ) * w) :=
      Complex.hasDerivAt_log hslit_t
    have h2 := hlogderiv.comp t h1
    have h3 : HasDerivAt (fun s : ℝ => -Complex.log (1 - (s:ℂ) * w))
        (-((1 - (t:ℂ) * w)⁻¹ * -w)) t := h2.neg
    have heq : -((1 - (t:ℂ) * w)⁻¹ * -w) = w / (1 - (t:ℂ) * w) := by
      rw [div_eq_mul_inv]; ring
    rwa [heq] at h3
  have hcont : ContinuousOn (fun t : ℝ => w / (1 - (t:ℂ) * w)) (Set.Icc 0 1) := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro t ht
      have := (hslit t ht)
      intro heq
      rw [heq] at this
      simp [Complex.slitPlane] at this
  have hFTC : ∫ t in (0:ℝ)..1, w / (1 - (t:ℂ) * w) =
      (-Complex.log (1 - (1:ℝ) * w)) - (-Complex.log (1 - (0:ℝ) * w)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => -Complex.log (1 - (s:ℂ) * w))
      (f' := fun t : ℝ => w / (1 - (t:ℂ) * w))
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact hderiv t ht
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hcont
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, sub_zero,
    Complex.log_one, neg_zero, sub_zero] at hFTC
  have hintg : ∀ t ∈ Set.Icc (0:ℝ) 1, w / (1 - (t:ℂ) * w) - w =
      (t:ℂ) * w^2 / (1 - (t:ℂ) * w) := by
    intro t ht
    have hne : (1:ℂ) - (t:ℂ) * w ≠ 0 := by
      intro heq
      have := hslit t ht
      rw [heq] at this
      simp [Complex.slitPlane] at this
    rw [← sub_eq_zero]
    have step1 : w / (1 - (t:ℂ) * w) - (t:ℂ) * w^2 / (1 - (t:ℂ) * w) =
        (w - (t:ℂ) * w^2) / (1 - (t:ℂ) * w) := div_sub_div_same w ((t:ℂ) * w^2) _
    have step2 : w - (t:ℂ) * w^2 = w * (1 - (t:ℂ) * w) := by ring
    have step3 : w / (1 - (t:ℂ) * w) - w - (t:ℂ) * w^2 / (1 - (t:ℂ) * w) =
        (w / (1 - (t:ℂ) * w) - (t:ℂ) * w^2 / (1 - (t:ℂ) * w)) - w := by ring
    rw [step3, step1, step2, mul_div_assoc, div_self hne, mul_one]
    ring
  have hintconst : ∫ t in (0:ℝ)..1, w = w := by
    simp [intervalIntegral.integral_const]
  have hsplit : ∫ t in (0:ℝ)..1, (w / (1 - (t:ℂ) * w) - w) =
      ∫ t in (0:ℝ)..1, ((t:ℂ) * w^2 / (1 - (t:ℂ) * w)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact hintg t ht
  have hlhs : ∫ t in (0:ℝ)..1, (w / (1 - (t:ℂ) * w) - w) = -Complex.log (1 - w) - w := by
    rw [intervalIntegral.integral_sub]
    · rw [hFTC, hintconst]
    · exact (hcont.mono (Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1) ▸ Set.Subset.refl _)).intervalIntegrable
    · exact intervalIntegrable_const
  have hkey : Complex.log (1 - w) + w = -(∫ t in (0:ℝ)..1, ((t:ℂ) * w^2 / (1 - (t:ℂ) * w))) := by
    have h1 : -Complex.log (1 - w) - w = ∫ t in (0:ℝ)..1, ((t:ℂ) * w^2 / (1 - (t:ℂ) * w)) := by
      rw [← hlhs, hsplit]
    linear_combination -h1
  rw [hkey, norm_neg]
  have hbound : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      ‖(t:ℂ) * w^2 / (1 - (t:ℂ) * w)‖ ≤ ‖w‖^2 / (1 - ‖w‖) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have ht0 : (0:ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hne : (1:ℂ) - (t:ℂ) * w ≠ 0 := by
      intro heq
      have := hslit t (Set.mem_Icc.mpr ⟨ht0, ht1⟩)
      rw [heq] at this
      simp [Complex.slitPlane] at this
    have hdenom : 1 - ‖w‖ ≤ ‖(1:ℂ) - (t:ℂ) * w‖ := by
      have h1 : ((1:ℂ) - (t:ℂ) * w).re ≤ ‖(1:ℂ) - (t:ℂ) * w‖ := by
        have := hre_le_norm ((1:ℂ) - (t:ℂ) * w)
        rw [abs_le] at this
        linarith [this.2]
      have h2 : 1 - ‖w‖ ≤ ((1:ℂ) - (t:ℂ) * w).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im]
        have h3 : t * w.re ≤ ‖w‖ := by
          have h4 := hre_le_norm w
          rw [abs_le] at h4
          nlinarith [h4.2]
        nlinarith [h3]
      linarith
    have hdenom_pos : (0:ℝ) < 1 - ‖w‖ := by linarith [hw]
    have htnorm : ‖(t:ℂ)‖ = t := by
      first
      | rw [Complex.norm_real]; exact abs_of_nonneg ht0
      | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ht0
      | simp [Complex.norm_eq_abs, abs_of_nonneg ht0]
    calc ‖(t:ℂ) * w^2 / (1 - (t:ℂ) * w)‖
        = t * ‖w‖^2 / ‖(1:ℂ) - (t:ℂ) * w‖ := by
          rw [norm_div, norm_mul, norm_pow, htnorm]
      _ ≤ t * ‖w‖^2 / (1 - ‖w‖) := by
          apply div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom
      _ ≤ 1 * ‖w‖^2 / (1 - ‖w‖) := by
          apply div_le_div_of_nonneg_right _ hdenom_pos.le
          nlinarith [sq_nonneg ‖w‖, ht1]
      _ = ‖w‖^2 / (1 - ‖w‖) := by ring
  have hfinal := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := (1:ℝ)) (C := ‖w‖^2 / (1 - ‖w‖))
      (f := fun t : ℝ => (t:ℂ) * w^2 / (1 - (t:ℂ) * w))
      (fun t ht => hbound t (by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact Set.Ioc_subset_Icc_self ht))
  simpa using hfinal

/-- Complex-z analogue of prime_correction_bound. -/
theorem prime_correction_bound_complex (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖(-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)‖
      ≤ 18 * (p:ℝ) ^ (-2*s) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a:ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z:ℂ) * (a:ℂ)‖ ≤ 2/3 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ 2 * (1/3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt1 : ‖(z:ℂ) * (a:ℂ)‖ < 1 := by linarith
  have hr1 := complex_log_bound ((z:ℂ) * (a:ℂ)) hza_lt1
  have hr2 := log_bound_combined a (by rw [abs_of_pos ha_pos]; linarith)
  have hr1bound : ‖z * (a:ℂ)‖^2 / (1 - ‖z * (a:ℂ)‖) ≤ 12 * a^2 := by
    have h1 : ‖z * (a:ℂ)‖ ≤ 2 * a := by
      rw [norm_mul, hane]; nlinarith [hz]
    have h2 : (1:ℝ)/3 ≤ 1 - ‖z * (a:ℂ)‖ := by linarith [hza_le]
    have h3 : ‖z * (a:ℂ)‖^2 ≤ 4 * a^2 := by
      nlinarith [h1, norm_nonneg (z * (a:ℂ))]
    calc ‖z * (a:ℂ)‖^2 / (1 - ‖z * (a:ℂ)‖) ≤ ‖z * (a:ℂ)‖^2 / (1/3) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h2
      _ = 3 * ‖z * (a:ℂ)‖^2 := by ring
      _ ≤ 3 * (4 * a^2) := by linarith [h3]
      _ = 12 * a^2 := by ring
  have hkey : (-Complex.log (1 - z * (a:ℂ))) + z * (Real.log (1 - a) : ℂ)
      = -(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)) +
          z * ((Real.log (1 - a) : ℂ) + (a:ℂ)) := by ring
  rw [hkey]
  have hstep1 : ‖-(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖
      ≤ ‖Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ := by
    have := norm_add_le (-(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)))
      (z * ((Real.log (1 - a) : ℂ) + (a:ℂ)))
    rwa [norm_neg] at this
  have hstep2 : ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ ≤ ‖z‖ * (3 * a^2) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have heq : ((Real.log (1 - a) : ℂ) + (a:ℂ)) = ((Real.log (1 - a) + a : ℝ):ℂ) := by
      push_cast; ring
    rw [heq]
    first
    | rw [Complex.norm_real]; exact hr2
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact hr2
  have hfinal_bound : ‖Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)‖ +
      ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ ≤ 12 * a^2 + ‖z‖ * (3 * a^2) := by
    linarith [hr1, hr1bound, hstep2]
  calc ‖-(Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖
      ≤ ‖Complex.log (1 - z * (a:ℂ)) + z * (a:ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a:ℂ))‖ := hstep1
    _ ≤ 12 * a^2 + ‖z‖ * (3 * a^2) := hfinal_bound
    _ ≤ 12 * a^2 + 2 * (3 * a^2) := by nlinarith [hz, sq_nonneg a]
    _ = 18 * a^2 := by ring
    _ = 18 * (p:ℝ) ^ (-2*s) := by
        rw [ha_def, ← Real.rpow_natCast ((p:ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
        ring_nf

/-- Complex-z analogue of prime_correction_summable. -/
theorem prime_correction_summable_complex (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => 18 * (p:ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (18:ℝ) * (p:ℝ) ^ (-2*s) =
        18 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      prime_correction_bound_complex (p:ℕ) p.property.2 s hs z hz)
    hcomp

/-- Complex-z analogue of prime_factor_sub_one_bound. -/
theorem prime_factor_sub_one_bound_complex (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖
      ≤ 36 * (p:ℝ) ^ (-2*s) := by
  set c : ℂ := (-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
    z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ) with hc_def
  have hp3 : 3 ≤ p := by omega
  have hbound : ‖c‖ ≤ 18 * (p:ℝ) ^ (-2*s) := prime_correction_bound_complex p hp3 s hs z hz
  have hle1 : 18 * (p:ℝ) ^ (-2*s) ≤ 1 := correction_le_one p hp s hs
  have hc1 : ‖c‖ ≤ 1 := le_trans hbound hle1
  calc ‖Complex.exp c - 1‖ ≤ 2 * ‖c‖ := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (18 * (p:ℝ) ^ (-2*s)) := by linarith [hbound]
    _ = 36 * (p:ℝ) ^ (-2*s) := by ring

/-- Complex-z analogue of prime_factor_sub_one_summable. -/
theorem prime_factor_sub_one_summable_complex (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 36 * (p:ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (36:ℝ) * (p:ℝ) ^ (-2*s) =
        36 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 36
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      prime_factor_sub_one_bound_complex (p:ℕ) p.property.2 s hs z hz)
    hcomp

/-- Complex-z analogue of prime_factor_eq_exp. -/
theorem prime_factor_eq_exp_complex (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
      Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a:ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z:ℂ) * (a:ℂ)‖ ≤ 2/3 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ 2 * (1/3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt : ‖(z:ℂ) * (a:ℂ)‖ < 1 := by linarith
  have h1za_ne : (1:ℂ) - z * (a:ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1:ℝ) = ‖z * (a:ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)):ℂ) ^ z =
      Complex.exp (Complex.log (((1 - a : ℝ)):ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne]
  have key : Complex.exp ((-Complex.log (1 - z * (a:ℂ))) +
      z * ((Real.log (1 - a) : ℝ):ℂ)) =
      (1 - z * (a:ℂ))⁻¹ * (((1 - a : ℝ)):ℂ) ^ z := by
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_log h1za_ne, hcpow, ← hlog1a,
      show z * Complex.log (((1 - a : ℝ)):ℂ) = Complex.log (((1 - a : ℝ)):ℂ) * z
        from mul_comm _ _]
  exact key.symm

/-- Complex-z analogue of prime_factor_multipliable. -/
theorem prime_factor_multipliable_complex (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable_complex s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + (Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
          (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
        1 + (Complex.exp ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) - 1) := by
    intro p
    have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
    rw [prime_factor_eq_exp_complex (p:ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult

/-- The complex-z tail of G₂: product over primes p≥5. -/
noncomputable def G2tailC (s : ℝ) (z : ℂ) : ℂ :=
  ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
    (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z

/-- G2tailC genuinely has this product as its value. -/
theorem G2tailC_hasProd (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z)
      (G2tailC s z) :=
  (prime_factor_multipliable_complex s hs z hz).hasProd

/-- The full complex G₂(s,z): p=3 factor times the convergent tail. -/
noncomputable def G2C (s : ℝ) (z : ℂ) : ℂ :=
  (1 - z * (((3:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
    (((1 - (3:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z * G2tailC s z

/-- Each G₂ per-prime factor is differentiable in z on |z|<2. -/
theorem prime_factor_differentiableOn (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
      (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) (Metric.ball 0 2) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza_lt : ‖z * (a:ℂ)‖ < 1 := by
    have hane : ‖(a:ℂ)‖ = a := by
      first
      | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
      | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
    rw [norm_mul, hane]
    nlinarith [hz, ha_le, ha_pos]
  have h1za_ne : (1:ℂ) - z * (a:ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1:ℝ) = ‖z * (a:ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · have hlin : DifferentiableAt ℂ (fun w : ℂ => (1:ℂ) - w * (a:ℂ)) z := by
      first
      | exact (differentiableAt_const (1:ℂ)).sub (differentiableAt_id.mul_const (a:ℂ))
      | exact (differentiableAt_const (1:ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a:ℂ))
    exact hlin.inv h1za_ne
  · first
    | exact differentiableAt_id.const_cpow (Or.inr h1a_ne)
    | exact differentiableAt_id.const_cpow (Or.inl h1a_ne)
    | exact DifferentiableAt.const_cpow differentiableAt_id (Or.inr h1a_ne)

/-- General fact: HasSum g a implies HasProd (exp∘g) (exp a). -/
theorem hasProd_exp_of_hasSum {ι : Type*} {g : ι → ℂ} {a : ℂ} (h : HasSum g a) :
    HasProd (fun i => Complex.exp (g i)) (Complex.exp a) := by
  have heq : ∀ t : Finset ι, Complex.exp (∑ i ∈ t, g i) = ∏ i ∈ t, Complex.exp (g i) := by
    intro t
    first
    | exact Complex.exp_sum t g
    | induction t using Finset.induction with
      | empty => simp
      | insert hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, Complex.exp_add, ih]
  have htendsto : Filter.Tendsto (fun t : Finset ι => Complex.exp (∑ i ∈ t, g i))
      Filter.atTop (nhds (Complex.exp a)) := (Complex.continuous_exp.tendsto a).comp h
  simp only [heq] at htendsto
  exact htendsto

/-- Each per-prime correction term is differentiable in z. -/
theorem correction_differentiableOn (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
      z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) (Metric.ball 0 2) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hane : ‖(a:ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_lt : ‖z * (a:ℂ)‖ < 1 := by
    rw [norm_mul, hane]; nlinarith [hz, ha_le, ha_pos]
  have hre_pos : (0:ℝ) < ((1:ℂ) - z * (a:ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    have hre_le_norm : |z.re| ≤ ‖z‖ := by
      have hns : z.re^2 ≤ Complex.normSq z := by
        have : Complex.normSq z = z.re^2 + z.im^2 := by
          rw [Complex.normSq_apply]; ring
        nlinarith [sq_nonneg z.im, this]
      have hnormsq : ‖z‖^2 = Complex.normSq z := by
        first
        | rw [Complex.norm_eq_abs, Complex.abs_apply, Real.sq_sqrt (Complex.normSq_nonneg z)]
        | rw [Complex.sq_norm]
        | rw [Complex.norm_sq_apply]
        | exact (Complex.normSq_eq_abs z).symm ▸ (Complex.sq_abs z)
        | rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]
      have hsq : z.re^2 ≤ ‖z‖^2 := by rw [hnormsq]; exact hns
      nlinarith [abs_nonneg z.re, norm_nonneg z, sq_abs z.re, hsq]
    have hre_le : z.re * a ≤ ‖z‖ * a := by
      rw [abs_le] at hre_le_norm
      nlinarith [hre_le_norm.2, ha_pos]
    nlinarith [hz, ha_pos, hre_le]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · apply DifferentiableAt.neg
    apply DifferentiableAt.clog
    · first
      | exact (differentiableAt_const (1:ℂ)).sub (differentiableAt_id.mul_const (a:ℂ))
      | exact (differentiableAt_const (1:ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a:ℂ))
    · exact Or.inl hre_pos
  · exact differentiableAt_id.mul_const _

/-- The sum of correction terms is differentiable in z on |z|<2. -/
theorem correction_sum_differentiableOn (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)))
      (Metric.ball 0 2) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 18 * (p:ℝ) ^ (-2*s))
  · have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (18:ℝ) * (p:ℝ) ^ (-2*s) =
        18 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  · intro p
    have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
    exact correction_differentiableOn (p:ℕ) hp3 s hs
  · exact Metric.isOpen_ball
  · intro p w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
    exact prime_correction_bound_complex (p:ℕ) hp3 s hs w hw.le

/-- G2tailC equals exp of the sum of correction terms. -/
theorem G2tailC_eq_exp_sum (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    G2tailC s z = Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  have hnormsum : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
    have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 18 * (p:ℝ) ^ (-2*s)) := by
      have h2s : -(2*s) < -1 := by linarith
      have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(2*s))) :=
        Real.summable_nat_rpow.mpr h2s
      have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p:ℕ):ℝ) ^ (-(2*s))) :=
        hbase.subtype _
      have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (18:ℝ) * (p:ℝ) ^ (-2*s) =
          18 * ((p:ℕ):ℝ) ^ (-(2*s)) := by
        intro p; ring_nf
      simp_rw [heq]
      exact hsub.mul_left 18
    apply Summable.of_nonneg_of_le
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => by
        have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
        exact prime_correction_bound_complex (p:ℕ) hp3 s hs z hz)
      hcomp
  have hsummable : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) :=
    Summable.of_norm hnormsum
  have hhassum := hsummable.hasSum
  have hhasprod_exp := hasProd_exp_of_hasSum hhassum
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, Complex.exp
      ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z := by
    intro p
    have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
    exact (prime_factor_eq_exp_complex (p:ℕ) hp3 s hs z hz).symm
  simp only [heq] at hhasprod_exp
  have hhasprod_G2 := G2tailC_hasProd s hs z hz
  exact (hhasprod_G2.unique hhasprod_exp)

/-- G2tailC is differentiable on the ball |z|<2. -/
theorem G2tailC_differentiableOn (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2tailC s z) (Metric.ball 0 2) := by
  have heq : ∀ z ∈ Metric.ball (0:ℂ) 2, G2tailC s z = Complex.exp
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ))) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact G2tailC_eq_exp_sum s hs z hz.le
  apply DifferentiableOn.congr _ heq
  exact Complex.differentiable_exp.comp_differentiableOn (correction_sum_differentiableOn s hs)

/-- G2C is differentiable on the ball |z|<2. -/
theorem G2C_differentiableOn (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2C s z) (Metric.ball 0 2) := by
  unfold G2C
  apply DifferentiableOn.mul
  · exact prime_factor_differentiableOn 3 (le_refl 3) s hs
  · exact G2tailC_differentiableOn s hs

/-- The i-th Taylor coefficient of G₂ at z=0: g_i(s) = G₂^(i)(0)/i!. -/
noncomputable def gCoeff (i : ℕ) (s : ℝ) : ℂ :=
  (iteratedDeriv i (fun z => G2C s z) 0) / (i.factorial : ℂ)

/-- If f(conj w) = conj(f w) for all w in an open conj-symmetric set U, and
    f has derivative f' at conj z₀ ∈ U, then f has derivative conj(f') at z₀. -/
theorem hasDerivAt_conj_of_symm {U : Set ℂ} (hUopen : IsOpen U)
    (hUconj : ∀ w ∈ U, (starRingEnd ℂ) w ∈ U)
    {f : ℂ → ℂ} (hsymm : ∀ w ∈ U, f ((starRingEnd ℂ) w) = (starRingEnd ℂ) (f w))
    {z₀ f' : ℂ} (hz₀ : z₀ ∈ U)
    (hf : HasDerivAt f f' ((starRingEnd ℂ) z₀)) :
    HasDerivAt f ((starRingEnd ℂ) f') z₀ := by
  have hz₀conj : (starRingEnd ℂ) z₀ ∈ U := hUconj z₀ hz₀
  have hfW : HasDerivWithinAt f f' U ((starRingEnd ℂ) z₀) := hf.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto] at hfW
  have hconj_cont : Filter.Tendsto (fun z : ℂ => (starRingEnd ℂ) z)
      (nhdsWithin z₀ U) (nhdsWithin ((starRingEnd ℂ) z₀) U) := by
    apply Filter.Tendsto.inf
    · exact (Complex.continuous_conj).continuousAt.tendsto
    · rw [Filter.tendsto_principal_principal]
      exact fun z hz => hUconj z hz
  have hcomp := hfW.comp hconj_cont
  have heq : ∀ z ∈ U, ‖z - z₀‖⁻¹ * ‖f z - f z₀ - (z - z₀) • (starRingEnd ℂ) f'‖ =
      ‖(starRingEnd ℂ) z - (starRingEnd ℂ) z₀‖⁻¹ *
        ‖f ((starRingEnd ℂ) z) - f ((starRingEnd ℂ) z₀) -
          ((starRingEnd ℂ) z - (starRingEnd ℂ) z₀) • f'‖ := by
    intro z hzU
    have h1 : f z = (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) := by
      have := hsymm ((starRingEnd ℂ) z) (hUconj z hzU)
      rwa [Complex.conj_conj] at this
    have h2 : f z₀ = (starRingEnd ℂ) (f ((starRingEnd ℂ) z₀)) := by
      have := hsymm ((starRingEnd ℂ) z₀) (hUconj z₀ hz₀)
      rwa [Complex.conj_conj] at this
    have hnorm_conj : ‖z - z₀‖ = ‖(starRingEnd ℂ) z - (starRingEnd ℂ) z₀‖ := by
      rw [← map_sub, Complex.norm_conj]
    have hbracket : f z - f z₀ - (z - z₀) • (starRingEnd ℂ) f' =
        (starRingEnd ℂ) (f ((starRingEnd ℂ) z) - f ((starRingEnd ℂ) z₀) -
          ((starRingEnd ℂ) z - (starRingEnd ℂ) z₀) • f') := by
      rw [h1, h2] at *
      simp only [smul_eq_mul, map_sub, map_mul, Complex.conj_conj]
    rw [hnorm_conj, hbracket, Complex.norm_conj]
  have heventually : (fun x' : ℂ => ‖(starRingEnd ℂ) x' - (starRingEnd ℂ) z₀‖⁻¹ *
        ‖f ((starRingEnd ℂ) x') - f ((starRingEnd ℂ) z₀) -
          ((starRingEnd ℂ) x' - (starRingEnd ℂ) z₀) • f'‖) =ᶠ[nhdsWithin z₀ U]
      (fun x' : ℂ => ‖x' - z₀‖⁻¹ * ‖f x' - f z₀ - (x' - z₀) • (starRingEnd ℂ) f'‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz using (heq z hz).symm
  have hfinal : Filter.Tendsto (fun z : ℂ => ‖z - z₀‖⁻¹ *
      ‖f z - f z₀ - (z - z₀) • (starRingEnd ℂ) f'‖) (nhdsWithin z₀ U) (nhds 0) :=
    Filter.Tendsto.congr' heventually hcomp
  rw [hUopen.nhdsWithin_eq hz₀] at hfinal
  rw [hasDerivAt_iff_tendsto]
  exact hfinal

/-- Each per-prime factor satisfies conjugate-reflection symmetry. -/
theorem prime_factor_conj_symm (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) (z : ℂ) :
    (1 - (starRingEnd ℂ) z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p:ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have hlog1a_real : (starRingEnd ℂ) (Complex.log (((1 - a : ℝ)):ℂ)) =
      Complex.log (((1 - a : ℝ)):ℂ) := by
    rw [hlog1a]; exact Complex.conj_ofReal _
  have hane_conj : (starRingEnd ℂ) ((a:ℂ)) = (a:ℂ) := Complex.conj_ofReal _
  have hcpow_symm : (((1 - a : ℝ)):ℂ) ^ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((((1 - a : ℝ)):ℂ) ^ z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne, Complex.cpow_def_of_ne_zero h1a_ne,
      ← Complex.exp_conj]
    congr 1
    rw [map_mul, hlog1a_real]
  have hinv_symm : (1 - (starRingEnd ℂ) z * (a:ℂ))⁻¹ =
      (starRingEnd ℂ) ((1 - z * (a:ℂ))⁻¹) := by
    rw [map_inv₀, map_sub, map_one, map_mul, hane_conj]
  rw [hcpow_symm, hinv_symm, ← map_mul]

/-- Each per-prime correction term satisfies conjugate-reflection symmetry
    on the ball |z|<2. -/
theorem correction_conj_symm (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ < 2) :
    (-Complex.log (1 - (starRingEnd ℂ) z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        (starRingEnd ℂ) z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ) =
      (starRingEnd ℂ) ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p:ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1/3 := by
    rw [ha_def]
    have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have h1 : (p:ℝ) ^ (-s) ≤ (p:ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p:ℝ) ^ (-1:ℝ) = 1 / (p:ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1:ℝ) / (p:ℝ) ≤ 1/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0:ℝ) < 1 - a := by linarith
  have hlog1a_real : (starRingEnd ℂ) ((Real.log (1 - a) : ℝ):ℂ) =
      ((Real.log (1 - a) : ℝ):ℂ) := Complex.conj_ofReal _
  have hane_conj : (starRingEnd ℂ) ((a:ℂ)) = (a:ℂ) := Complex.conj_ofReal _
  have hre_pos : ∀ w : ℂ, ‖w‖ < 2 → (0:ℝ) < ((1:ℂ) - w * (a:ℂ)).re := by
    intro w hw
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    have hre_le_norm : |w.re| ≤ ‖w‖ := by
      have hns : w.re^2 ≤ Complex.normSq w := by
        have : Complex.normSq w = w.re^2 + w.im^2 := by
          rw [Complex.normSq_apply]; ring
        nlinarith [sq_nonneg w.im, this]
      have hnormsq : ‖w‖^2 = Complex.normSq w := by
        first
        | rw [Complex.norm_eq_abs, Complex.abs_apply, Real.sq_sqrt (Complex.normSq_nonneg w)]
        | rw [Complex.sq_norm]
        | rw [Complex.norm_sq_apply]
        | exact (Complex.normSq_eq_abs w).symm ▸ (Complex.sq_abs w)
        | rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w)]
      have hsq : w.re^2 ≤ ‖w‖^2 := by rw [hnormsq]; exact hns
      nlinarith [abs_nonneg w.re, norm_nonneg w, sq_abs w.re, hsq]
    have hre_le : w.re * a ≤ ‖w‖ * a := by
      rw [abs_le] at hre_le_norm
      nlinarith [hre_le_norm.2, ha_pos]
    nlinarith [hw, ha_pos, hre_le]
  have harg_ne : ∀ w : ℂ, ‖w‖ < 2 →
      ((1:ℂ) - w * (a:ℂ)).arg ≠ Real.pi := by
    intro w hw harg
    have := hre_pos w hw
    rw [Complex.arg_eq_pi_iff] at harg
    linarith [harg.1]
  have hlog_conj : Complex.log ((starRingEnd ℂ) (1 - z * (a:ℂ))) =
      (starRingEnd ℂ) (Complex.log (1 - z * (a:ℂ))) := by
    rw [Complex.log_conj (1 - z * (a:ℂ)) (harg_ne z hz)]
  have hconj_sub : (starRingEnd ℂ) (1 - z * (a:ℂ)) = 1 - (starRingEnd ℂ) z * (a:ℂ) := by
    rw [map_sub, map_one, map_mul, hane_conj]
  rw [← hconj_sub, hlog_conj]
  simp only [map_neg, map_add, map_mul, hlog1a_real]

/-- The correction-term sum satisfies conjugate-reflection symmetry. -/
theorem correction_sum_conj_symm (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ < 2) :
    ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - (starRingEnd ℂ) z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
        (starRingEnd ℂ) z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (starRingEnd ℂ) (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ((-Complex.log (1 - z * (((p:ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p:ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  rw [RCLike.conj_tsum]
  apply tsum_congr
  intro p
  have hp3 : 3 ≤ (p:ℕ) := by have := p.property.2; omega
  exact correction_conj_symm (p:ℕ) hp3 s hs z hz

/-- G2tailC satisfies conjugate-reflection symmetry on the ball |z|<2. -/
theorem G2tailC_conj_symm (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ < 2) :
    G2tailC s ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G2tailC s z) := by
  have hzconj_le : ‖(starRingEnd ℂ) z‖ ≤ 2 := by
    rw [Complex.norm_conj]; exact hz.le
  rw [G2tailC_eq_exp_sum s hs ((starRingEnd ℂ) z) hzconj_le,
      G2tailC_eq_exp_sum s hs z hz.le, ← Complex.exp_conj]
  congr 1
  exact correction_sum_conj_symm s hs z hz

/-- G2C satisfies conjugate-reflection symmetry on the ball |z|<2. -/
theorem G2C_conj_symm (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ < 2) :
    G2C s ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G2C s z) := by
  unfold G2C
  have hcast : ((3:ℕ):ℝ) = (3:ℝ) := by norm_num
  have hsymm3 := prime_factor_conj_symm 3 (le_refl 3) s hs z
  rw [hcast] at hsymm3
  rw [hsymm3, G2tailC_conj_symm s hs z hz, ← map_mul]

/-- Conjugate-reflection symmetry AND differentiability both propagate to
    every iterated derivative. -/
theorem iteratedDeriv_conj_symm {U : Set ℂ} (hUopen : IsOpen U)
    (hUconj : ∀ w ∈ U, (starRingEnd ℂ) w ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hsymm : ∀ w ∈ U, f ((starRingEnd ℂ) w) = (starRingEnd ℂ) (f w)) :
    ∀ n : ℕ, (∀ w ∈ U, iteratedDeriv n f ((starRingEnd ℂ) w) =
        (starRingEnd ℂ) (iteratedDeriv n f w)) ∧
      DifferentiableOn ℂ (iteratedDeriv n f) U := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using hsymm
    · simpa using hf
  | succ n ih =>
    obtain ⟨hsymm_n, hdiff_n⟩ := ih
    have hdiff_succ : DifferentiableOn ℂ (iteratedDeriv (n+1) f) U := by
      rw [iteratedDeriv_succ]
      exact hdiff_n.analyticOnNhd hUopen |>.deriv.differentiableOn
    refine ⟨?_, hdiff_succ⟩
    intro w hw
    have hderiv_symm := hasDerivAt_conj_of_symm hUopen hUconj hsymm_n hw
      ((hdiff_n ((starRingEnd ℂ) w) (hUconj w hw)).differentiableAt
        (hUopen.mem_nhds (hUconj w hw))).hasDerivAt
    rw [iteratedDeriv_succ]
    have hstep := hderiv_symm.deriv
    have hstep2 : (starRingEnd ℂ) (deriv (iteratedDeriv n f) w) =
        deriv (iteratedDeriv n f) ((starRingEnd ℂ) w) := by
      rw [hstep, Complex.conj_conj]
    exact hstep2.symm

/-- gCoeff is real-valued: culmination of the Schwarz-reflection arc. -/
theorem gCoeff_real (i : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    (starRingEnd ℂ) (gCoeff i s) = gCoeff i s := by
  unfold gCoeff
  have hUopen : IsOpen (Metric.ball (0:ℂ) 2) := Metric.isOpen_ball
  have hUconj : ∀ w ∈ Metric.ball (0:ℂ) 2, (starRingEnd ℂ) w ∈ Metric.ball (0:ℂ) 2 := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    rwa [Complex.norm_conj]
  have hf : DifferentiableOn ℂ (fun z => G2C s z) (Metric.ball (0:ℂ) 2) :=
    G2C_differentiableOn s hs
  have hsymm : ∀ w ∈ Metric.ball (0:ℂ) 2,
      G2C s ((starRingEnd ℂ) w) = (starRingEnd ℂ) (G2C s w) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact G2C_conj_symm s hs w hw
  have h0 : (0:ℂ) ∈ Metric.ball (0:ℂ) 2 := by
    rw [Metric.mem_ball]; simp
  have hind := (iteratedDeriv_conj_symm hUopen hUconj hf hsymm i).1 0 h0
  simp only [map_zero] at hind
  rw [map_div₀]
  congr 1
  · exact hind.symm
  · exact Complex.conj_ofReal _

/-- gCoeff literally equals its own real part (embedded in ℂ). -/
theorem gCoeff_eq_ofReal (i : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    gCoeff i s = (((gCoeff i s).re : ℝ) : ℂ) := by
  have hreal := gCoeff_real i s hs
  have him : (gCoeff i s).im = 0 := by
    have := Complex.conj_eq_iff_im.mp hreal
    exact this
  apply Complex.ext
  · simp
  · simp [him]

open scoped Classical in
/-- The k-almost-prime counting function, restricted to numbers whose
    smallest prime factor is ≥ p₀ -- the standard auxiliary object needed
    for the classical elementary induction on k. -/
noncomputable def piKFrom (k : ℕ) (x : ℝ) (p₀ : ℕ) : ℕ :=
  (Finset.Icc 2 ⌊x⌋₊).filter
    (fun n => bigOmega n = k ∧ ∀ q, q.Prime → q ∣ n → p₀ ≤ q) |>.card

/-- piK is the p₀=2 case of piKFrom. -/
theorem piK_eq_piKFrom_two (k : ℕ) (x : ℝ) : piK k x = piKFrom k x 2 := by
  classical
  unfold piK piKFrom
  congr 1
  apply Finset.filter_congr
  intro n hn
  constructor
  · intro h
    exact ⟨h, fun q hq _ => hq.two_le⟩
  · intro h
    exact h.1

/-- The key recursive identity: a (k+1)-almost-prime n with smallest
    factor ≥p₀ corresponds bijectively to (p, m) where p=n.minFac (p≥p₀)
    and m=n/p is a k-almost-prime with smallest factor ≥p. Valid for k≥1. -/
theorem piKFrom_succ_eq (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (p₀ : ℕ) (hx : 2 ≤ x) :
    piKFrom (k+1) x p₀ =
      ∑ p ∈ (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime),
        piKFrom k (x / p) p := by
  classical
  unfold piKFrom
  rw [Finset.card_eq_sum_card_fiberwise (f := Nat.minFac)
    (t := (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime))]
  · apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpMem, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp0, hplex⟩ := Finset.mem_Icc.mp hpMem
    have hp2 : 2 ≤ p := hpp.two_le
    apply Finset.card_bij' (fun n _ => n / p) (fun m _ => p * m)
    · intro n hn
      obtain ⟨hnInS, hnminFac⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnMem, hnO, hnfac⟩ := Finset.mem_filter.mp hnInS
      obtain ⟨hn2, hnx⟩ := Finset.mem_Icc.mp hnMem
      have hpdvd : p ∣ n := hnminFac ▸ Nat.minFac_dvd n
      have hnpk : bigOmega (n / p) = k := by
        have hOmega : bigOmega n = bigOmega (n/p) + bigOmega p := by
          conv_lhs => rw [← Nat.div_mul_cancel hpdvd]
          exact bigOmega_mul (n/p) p (by
            rcases Nat.eq_zero_or_pos (n/p) with h0|h0
            · exfalso
              have hcontra : n = 0 := by
                have := Nat.div_mul_cancel hpdvd
                rw [h0, zero_mul] at this
                omega
              omega
            · omega) hpp.pos.ne'
        have hOmegap : bigOmega p = 1 := by
          unfold bigOmega; rw [hpp.factorization]; simp
        omega
      have hnp2 : 2 ≤ n / p := by
        by_contra h
        push_neg at h
        interval_cases (n / p)
        · simp [bigOmega] at hnpk; omega
        · have : bigOmega 1 = 0 := by simp [bigOmega]
          omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnp2, ?_⟩, hnpk, ?_⟩
      · have hcast : ((n / p : ℕ) : ℝ) = (n:ℝ) / p := by
          rw [eq_div_iff (by positivity)]
          exact_mod_cast Nat.div_mul_cancel hpdvd
        rw [Nat.le_floor_iff (by positivity), hcast]
        calc (n:ℝ)/p ≤ (⌊x⌋₊:ℝ)/p := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact_mod_cast hnx
          _ ≤ x / p := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact Nat.floor_le (by positivity)
      · intro q hq hqdvd
        have hqdvdn : q ∣ n := hqdvd.trans (Nat.div_dvd_of_dvd hpdvd)
        rw [← hnminFac]
        exact Nat.minFac_le_of_dvd hq.two_le hqdvdn
    · intro m hm
      obtain ⟨hmMem, hmO, hmfac⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm2, hmx⟩ := Finset.mem_Icc.mp hmMem
      have hOmegap : bigOmega p = 1 := by
        unfold bigOmega; rw [hpp.factorization]; simp
      have hOmegapm : bigOmega (p * m) = k + 1 := by
        rw [bigOmega_mul p m hpp.pos.ne' (by omega), hOmegap, hmO]; ring
      have hminFacpm : (p * m).minFac = p := by
        have hle : (p * m).minFac ≤ p := Nat.minFac_le_of_dvd hp2 (Dvd.intro m rfl)
        have hge : p ≤ (p * m).minFac := by
          have hprime : (p*m).minFac.Prime := Nat.minFac_prime (by
            intro h; rw [h] at hOmegapm; simp [bigOmega] at hOmegapm)
          have hdvd : (p * m).minFac ∣ p * m := Nat.minFac_dvd _
          rcases (Nat.Prime.dvd_mul hprime).mp hdvd with hdp | hdm
          · exact ((Nat.prime_dvd_prime_iff_eq hprime hpp).mp hdp).symm.le
          · exact hmfac _ hprime hdm
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by nlinarith [hpp.two_le], ?_⟩, hOmegapm, ?_⟩, hminFacpm⟩
      · rw [Nat.le_floor_iff (by positivity)] at hmx ⊢
        have : (m:ℝ) ≤ x / p := hmx
        have hpm : (p * m : ℝ) ≤ x := by
          rw [le_div_iff₀ (by positivity)] at this
          push_cast
          nlinarith
        exact_mod_cast hpm
      · intro q hq hqdvd
        rcases (Nat.Prime.dvd_mul hq).mp hqdvd with hdp | hdm
        · rw [(Nat.prime_dvd_prime_iff_eq hq hpp).mp hdp]; exact hp0
        · exact hp0.trans (hmfac _ hq hdm)
    · intro n hn
      obtain ⟨hnInS, hnminFac⟩ := Finset.mem_filter.mp hn
      exact Nat.mul_div_cancel' (hnminFac ▸ Nat.minFac_dvd n)
    · intro m hm
      exact Nat.mul_div_cancel_left m hpp.pos
  · intro n hn
    obtain ⟨hnMem, hnO, hnfac⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn2, hnx⟩ := Finset.mem_Icc.mp hnMem
    have hn1 : n ≠ 1 := by omega
    have hpp := Nat.minFac_prime hn1
    have hpdvd := Nat.minFac_dvd n
    have hp0 := hnfac _ hpp hpdvd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp0, ?_⟩, hpp⟩
    have hple : n.minFac ≤ n := Nat.minFac_le (by omega)
    omega

/-- bigOmega n = 1 iff n is prime. -/
theorem bigOmega_eq_one_iff (n : ℕ) : bigOmega n = 1 ↔ n.Prime := by
  constructor
  · intro hn1
    have hn2 : 2 ≤ n := by
      by_contra h
      push_neg at h
      interval_cases n <;> simp [bigOmega] at hn1
    set p := n.minFac with hp_def
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpdvd : p ∣ n := Nat.minFac_dvd n
    have hOmega : bigOmega n = bigOmega p + bigOmega (n / p) := by
      conv_lhs => rw [← Nat.div_mul_cancel hpdvd, mul_comm]
      exact bigOmega_mul p (n/p) hpp.pos.ne' (by
        rcases Nat.eq_zero_or_pos (n/p) with h0|h0
        · exfalso
          have : n = 0 := by
            have := Nat.div_mul_cancel hpdvd
            rw [h0, zero_mul] at this
            omega
          omega
        · omega)
    have hOmegap : bigOmega p = 1 := by
      unfold bigOmega; rw [hpp.factorization]; simp
    have hOmegam : bigOmega (n / p) = 0 := by omega
    have hm1 : n / p = 1 := by
      by_contra hm
      have hm2 : 2 ≤ n / p := by
        rcases Nat.eq_zero_or_pos (n/p) with h0|h0
        · exfalso
          have hcontra : n = 0 := by
            have heq := Nat.div_mul_cancel hpdvd
            rw [h0, zero_mul] at heq
            omega
          omega
        · omega
      set q := (n/p).minFac with hq_def
      have hqp : q.Prime := Nat.minFac_prime (by omega)
      have hqdvd : q ∣ (n/p) := Nat.minFac_dvd (n/p)
      have hOmegam2 : bigOmega (n/p) = bigOmega q + bigOmega ((n/p) / q) := by
        conv_lhs => rw [← Nat.div_mul_cancel hqdvd, mul_comm]
        exact bigOmega_mul q ((n/p)/q) hqp.pos.ne' (by
          rcases Nat.eq_zero_or_pos ((n/p)/q) with h0'|h0'
          · exfalso
            have heq2 : n/p = 0 := by
              have heq := Nat.div_mul_cancel hqdvd
              rw [h0', zero_mul] at heq
              omega
            omega
          · omega)
      have hOmegaq : bigOmega q = 1 := by
        unfold bigOmega; rw [hqp.factorization]; simp
      omega
    have : n = p := by
      have := Nat.div_mul_cancel hpdvd
      rw [hm1, one_mul] at this
      omega
    rwa [this]
  · intro hpp
    unfold bigOmega
    rw [hpp.factorization]
    simp

/-- piK(1,x) equals Nat.primeCounting ⌊x⌋₊. -/
theorem piK_one_eq_primeCounting (x : ℝ) : piK 1 x = Nat.primeCounting ⌊x⌋₊ := by
  unfold piK Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  rw [bigOmega_eq_one_iff]
  constructor
  · rintro ⟨⟨_, hnx⟩, hprime⟩
    exact ⟨by omega, hprime⟩
  · rintro ⟨hnx, hprime⟩
    exact ⟨⟨hprime.two_le, by omega⟩, hprime⟩

/-- piK_bound's k=1 base case. -/
theorem sum_log_prime_le_primorial (n : ℕ) :
    (∑ p ∈ Finset.range (n+1) with Nat.Prime p, Real.log p) ≤ n * Real.log 4 := by
  have h1 : (primorial n : ℝ) ≤ 4 ^ n := by exact_mod_cast primorial_le_four_pow n
  have hpos : (0:ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have h2 : Real.log (primorial n : ℝ) ≤ Real.log ((4:ℝ) ^ n) := by
    apply Real.log_le_log hpos h1
  rw [Real.log_pow] at h2
  have h3 : Real.log (primorial n : ℝ) =
      ∑ p ∈ Finset.range (n+1) with Nat.Prime p, Real.log p := by
    unfold primorial
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos.ne'
  linarith [h3 ▸ h2]

/-- Primes in (√n, n] each contribute ≥ log(√n) to the sum. -/
theorem sum_log_prime_ge_sqrt_range (n : ℕ) (hn : 4 ≤ n) :
    (∑ p ∈ Finset.range (n+1) with Nat.Prime p, Real.log p) ≥
      ((Nat.primeCounting n : ℝ) - Nat.primeCounting ⌊Real.sqrt n⌋₊) *
        Real.log (Real.sqrt n) := by
  have hsqrt_le : Real.sqrt n ≤ n := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc Real.sqrt n ≤ Real.sqrt (n*n) := by
          apply Real.sqrt_le_sqrt; nlinarith [hn1]
      _ = n := by rw [show (n:ℝ)*n = n^2 by ring, Real.sqrt_sq (by positivity)]
  have hfloor_le : ⌊Real.sqrt n⌋₊ ≤ n := by
    have h1 : (⌊Real.sqrt n⌋₊ : ℝ) ≤ Real.sqrt n := Nat.floor_le (by positivity)
    have h2 : (⌊Real.sqrt n⌋₊ : ℝ) ≤ n := h1.trans hsqrt_le
    exact_mod_cast h2
  have hsub : (Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime ⊆
      (Finset.range (n+1)).filter Nat.Prime := by
    apply Finset.filter_subset_filter
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hcard_eq : ((Finset.range (n+1)).filter Nat.Prime).card = Nat.primeCounting n := by
    rw [← Nat.primesLE_eq_filter_range]
    exact Nat.primesLE_card_eq_primeCounting n
  have hcard_eq2 : ((Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime).card =
      Nat.primeCounting ⌊Real.sqrt n⌋₊ := by
    rw [← Nat.primesLE_eq_filter_range]
    exact Nat.primesLE_card_eq_primeCounting _
  have hdiff_card : ((Finset.range (n+1)).filter Nat.Prime \
      (Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime).card =
      Nat.primeCounting n - Nat.primeCounting ⌊Real.sqrt n⌋₊ := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard_eq, hcard_eq2]
  have hlarge_ge : ∀ p ∈ (Finset.range (n+1)).filter Nat.Prime \
      (Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime,
      Real.log (Real.sqrt n) ≤ Real.log p := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_filter, Finset.mem_range] at hp1
    rw [Finset.mem_filter, Finset.mem_range] at hp2
    apply Real.log_le_log (by positivity)
    have hpp : ⌊Real.sqrt n⌋₊ < p := by
      by_contra h
      push_neg at h
      exact hp2 ⟨Nat.lt_succ_of_le h, hp1.2⟩
    calc Real.sqrt n ≤ (⌊Real.sqrt n⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
      _ ≤ p := by exact_mod_cast hpp
  have hsum_split := Finset.sum_le_sum hlarge_ge
  rw [Finset.sum_const, hdiff_card, nsmul_eq_mul] at hsum_split
  have hfull_eq : ∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, Real.log p =
      ∑ p ∈ (Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime, Real.log p +
        ∑ p ∈ (Finset.range (n+1)).filter Nat.Prime \
          (Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime, Real.log p := by
    rw [← Finset.sum_sdiff hsub]
    ring
  rw [hfull_eq]
  have hsmall_nonneg : 0 ≤ ∑ p ∈ (Finset.range (⌊Real.sqrt n⌋₊ + 1)).filter Nat.Prime,
      Real.log p := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  have hmono : ⌊Real.sqrt n⌋₊.primeCounting ≤ n.primeCounting :=
    Nat.monotone_primeCounting hfloor_le
  have hcast : ((n.primeCounting - ⌊Real.sqrt n⌋₊.primeCounting : ℕ) : ℝ) =
      (n.primeCounting : ℝ) - ⌊Real.sqrt n⌋₊.primeCounting :=
    Nat.cast_sub hmono
  rw [hcast] at hsum_split
  nlinarith [hsum_split, hsmall_nonneg]

/-- Our own reconstruction of the Chebyshev-type explicit upper bound. -/
theorem primeCounting_le_bound_own (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ Real.sqrt n + (n * Real.log 4) / Real.log (Real.sqrt n) := by
  have h1 := sum_log_prime_le_primorial n
  have h2 := sum_log_prime_ge_sqrt_range n hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hlogsqrt_pos : 0 < Real.log (Real.sqrt n) := by
    apply Real.log_pos
    have : (2:ℝ) ≤ Real.sqrt n := by
      rw [show (2:ℝ) = Real.sqrt 4 by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      exact_mod_cast hn
    linarith
  have hcombined : ((Nat.primeCounting n : ℝ) - ⌊Real.sqrt n⌋₊.primeCounting) *
      Real.log (Real.sqrt n) ≤ n * Real.log 4 := by linarith
  have htrivial : (⌊Real.sqrt n⌋₊.primeCounting : ℝ) ≤ Real.sqrt n := by
    have h3 : ⌊Real.sqrt n⌋₊.primeCounting ≤ ⌊Real.sqrt n⌋₊ := by
      have := Nat.primesLE_card_eq_primeCounting ⌊Real.sqrt n⌋₊
      rw [← this]
      calc (Nat.primesLE ⌊Real.sqrt n⌋₊).card ≤ (Finset.Icc 2 ⌊Real.sqrt n⌋₊).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Nat.mem_primesLE] at hx
            exact Finset.mem_Icc.mpr ⟨hx.2.two_le, hx.1⟩
        _ ≤ ⌊Real.sqrt n⌋₊ := by simp
    calc (⌊Real.sqrt n⌋₊.primeCounting : ℝ) ≤ (⌊Real.sqrt n⌋₊ : ℝ) := by exact_mod_cast h3
      _ ≤ Real.sqrt n := Nat.floor_le (by positivity)
  have := (div_le_div_iff_of_pos_right hlogsqrt_pos).mpr hcombined
  rw [mul_div_assoc, div_self hlogsqrt_pos.ne', mul_one] at this
  linarith [htrivial, this]

theorem piK_bound_one :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      (piK 1 x : ℝ) ≤ C * x * (Real.log (Real.log x)) ^ (1 - 1) / Real.log x := by
  use 2 + 4 * Real.log 4 + 10
  constructor
  · positivity
  · intro x hx
    rw [piK_one_eq_primeCounting]
    norm_num
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    rcases le_total 4 x with hx4 | hx4
    · have hfloor_ge : (⌊x⌋₊ : ℝ) ≥ x / 2 := by
        have h1 : (⌊x⌋₊ : ℝ) > x - 1 := by
          have := Nat.sub_one_lt_floor x
          linarith [Nat.floor_le (show (0:ℝ) ≤ x by linarith)]
        linarith
      have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hfloor2 : (2:ℝ) ≤ ⌊x⌋₊ := by linarith
      have hlogfloor_pos : 0 < Real.log ⌊x⌋₊ := Real.log_pos (by exact_mod_cast hfloor2)
      have hlog4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx4
      have hlogfloor_ge : Real.log ⌊x⌋₊ ≥ Real.log x / 2 := by
        have hge : Real.log ⌊x⌋₊ ≥ Real.log (x/2) := Real.log_le_log (by linarith) hfloor_ge
        have heq : Real.log (x/2) = Real.log x - Real.log 2 := by
          rw [Real.log_div (by linarith) (by norm_num)]
        have hlog2 : Real.log 2 ≤ Real.log x / 2 := by
          have : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
          linarith
        linarith
      have hfloor4' : 4 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx4)
      have hbound_own := primeCounting_le_bound_own ⌊x⌋₊ hfloor4'
      have hlogsqrt_eq : Real.log (Real.sqrt ⌊x⌋₊) = Real.log ⌊x⌋₊ / 2 :=
        Real.log_sqrt (by linarith)
      have hbound : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
          Real.sqrt ⌊x⌋₊ + (2 * ⌊x⌋₊ * Real.log 4) / Real.log ⌊x⌋₊ := by
        rw [hlogsqrt_eq] at hbound_own
        have heq2 : (⌊x⌋₊:ℝ) * Real.log 4 / (Real.log ⌊x⌋₊ / 2) =
            2 * ⌊x⌋₊ * Real.log 4 / Real.log ⌊x⌋₊ := by
          field_simp
        linarith [hbound_own, heq2]
      have hsqrt_le : Real.sqrt ⌊x⌋₊ ≤ 2 * ⌊x⌋₊ / Real.log ⌊x⌋₊ := by
        rw [le_div_iff₀ hlogfloor_pos]
        have hlogsqrt : Real.log ⌊x⌋₊ ≤ 2 * Real.sqrt ⌊x⌋₊ := by
          have hle : Real.log (Real.sqrt ⌊x⌋₊) ≤ Real.sqrt ⌊x⌋₊ :=
            Real.log_le_self (by positivity)
          calc Real.log ⌊x⌋₊ = 2 * Real.log (Real.sqrt ⌊x⌋₊) := by
                rw [hlogsqrt_eq]; ring
            _ ≤ 2 * Real.sqrt ⌊x⌋₊ := by linarith
        calc Real.sqrt ⌊x⌋₊ * Real.log ⌊x⌋₊ ≤ Real.sqrt ⌊x⌋₊ * (2 * Real.sqrt ⌊x⌋₊) := by
              apply mul_le_mul_of_nonneg_left hlogsqrt (Real.sqrt_nonneg _)
          _ = 2 * ⌊x⌋₊ := by
              rw [← mul_assoc, mul_comm (Real.sqrt ⌊x⌋₊) 2, mul_assoc,
                Real.mul_self_sqrt (by linarith)]
      have hcombined : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
          2 * ⌊x⌋₊ * (1 + Real.log 4) / Real.log ⌊x⌋₊ := by
        have heq : 2 * ⌊x⌋₊ / Real.log ⌊x⌋₊ + 2 * ⌊x⌋₊ * Real.log 4 / Real.log ⌊x⌋₊ =
            2 * ⌊x⌋₊ * (1 + Real.log 4) / Real.log ⌊x⌋₊ := by
          field_simp
        linarith [hbound, hsqrt_le, heq]
      have hhalve : 2 * ⌊x⌋₊ * (1 + Real.log 4) / Real.log ⌊x⌋₊ ≤
          4 * ⌊x⌋₊ * (1 + Real.log 4) / Real.log x := by
        rw [div_le_div_iff₀ hlogfloor_pos hlogx_pos]
        have hpos : 0 ≤ (1 + Real.log 4) := by
          have : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          linarith
        have hnn : (0:ℝ) ≤ 4 * (⌊x⌋₊:ℝ) * (1 + Real.log 4) := by
          have : (0:ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg ⌊x⌋₊
          nlinarith [this, hpos]
        nlinarith [mul_le_mul_of_nonneg_left hlogfloor_ge hnn]
      have hxbound : 4 * ⌊x⌋₊ * (1 + Real.log 4) / Real.log x ≤
          4 * x * (1 + Real.log 4) / Real.log x := by
        have hpos : (0:ℝ) ≤ (1 + Real.log 4) := by
          have : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          linarith
        have hle : 4 * (⌊x⌋₊:ℝ) * (1 + Real.log 4) ≤ 4 * x * (1 + Real.log 4) := by
          nlinarith [hfloor_le, hpos]
        exact div_le_div_of_nonneg_right hle hlogx_pos.le
      have hid : 4 * x * (1 + Real.log 4) / Real.log x =
          (4 + 4 * Real.log 4) * x / Real.log x := by
        field_simp
      have hfinal : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
          (2 + 4 * Real.log 4 + 10) * x / Real.log x := by
        rw [hid] at hxbound
        have hxpos : 0 ≤ x / Real.log x := by positivity
        have hle_const : (4 + 4 * Real.log 4 : ℝ) ≤ 2 + 4 * Real.log 4 + 10 := by linarith
        have hconst : (4 + 4 * Real.log 4) * x / Real.log x ≤
            (2 + 4 * Real.log 4 + 10) * x / Real.log x := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right hle_const hxpos
        linarith [hcombined, hhalve, hxbound, hconst]
      exact hfinal
    · have hfloor_le4 : (⌊x⌋₊:ℝ) ≤ 4 := (Nat.floor_le (by linarith)).trans hx4
      have hfloor_le4' : ⌊x⌋₊ ≤ 4 := by exact_mod_cast hfloor_le4
      have hpc_le : Nat.primeCounting ⌊x⌋₊ ≤ Nat.primeCounting 4 :=
        Nat.monotone_primeCounting hfloor_le4'
      have hpc4 : Nat.primeCounting 4 = 2 := by decide
      rw [hpc4] at hpc_le
      have hpc_le' : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 := by exact_mod_cast hpc_le
      have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have hlogx_le : Real.log x ≤ Real.log 4 := Real.log_le_log (by linarith) hx4
      have hbound_small : (3:ℝ) / Real.log 4 ≤ x / Real.log x := by
        rw [div_le_div_iff₀ hlog4_pos hlogx_pos]
        nlinarith [hlogx_le, hx]
      have h2le : (2:ℝ) ≤ (2 + 4 * Real.log 4 + 10) * (3 / Real.log 4) := by
        rw [← mul_div_assoc, le_div_iff₀ hlog4_pos]
        nlinarith [hlog4_pos]
      have hstep : (2 + 4 * Real.log 4 + 10) * (3 / Real.log 4) ≤
          (2 + 4 * Real.log 4 + 10) * (x / Real.log x) := by
        apply mul_le_mul_of_nonneg_left hbound_small
        positivity
      have hfinal2 : (2:ℝ) ≤ (2 + 4 * Real.log 4 + 10) * x / Real.log x := by
        rw [mul_div_assoc]
        linarith [h2le, hstep]
      linarith [hpc_le', hfinal2]

/-- Derivative of h(t) := (x/t)/log(x/t). -/
theorem hasDerivAt_ratio_log (x t : ℝ) (htpos : 0 < t) (hxt : 1 < x / t) :
    ∃ d : ℝ, HasDerivAt (fun s => (x / s) / Real.log (x / s)) d t ∧
      d = (x / t ^ 2) * (1 - Real.log (x / t)) / (Real.log (x / t)) ^ 2 := by
  have htne : t ≠ 0 := htpos.ne'
  have hu : HasDerivAt (fun s => x / s) (x * -(t^2)⁻¹) t := by
    have h1 : HasDerivAt (fun s : ℝ => s⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv htne
    have h2 := h1.const_mul x
    have heq : (fun s : ℝ => x / s) = (fun s : ℝ => x * s⁻¹) := by
      funext s; rw [div_eq_mul_inv]
    rw [heq]
    exact h2
  have hxpos : 0 < x := by
    have hposdiv : 0 < x / t := by linarith
    by_contra hxle
    push_neg at hxle
    have : x / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg hxle htpos.le
    linarith
  have hxt_ne : x / t ≠ 0 := by positivity
  have hv : HasDerivAt (fun s => Real.log (x / s)) ((x * -(t^2)⁻¹) / (x/t)) t :=
    hu.log hxt_ne
  have hvne : Real.log (x / t) ≠ 0 := ne_of_gt (Real.log_pos hxt)
  have hfinal := hu.div hv hvne
  refine ⟨_, hfinal, ?_⟩
  have htsq : t ^ 2 ≠ 0 := pow_ne_zero 2 htne
  have hxtne : x / t ≠ 0 := hxt_ne
  field_simp
  ring

/-- DifferentiableAt version of hasDerivAt_ratio_log. -/
theorem differentiableAt_ratio_log (x t : ℝ) (htpos : 0 < t) (hxt : 1 < x / t) :
    DifferentiableAt ℝ (fun s => (x / s) / Real.log (x / s)) t := by
  obtain ⟨d, hd, _⟩ := hasDerivAt_ratio_log x t htpos hxt
  exact hd.differentiableAt

/-- deriv f equals our explicit closed form pointwise. -/
theorem deriv_ratio_log_eq (x t : ℝ) (htpos : 0 < t) (hxt : 1 < x / t) :
    deriv (fun s => (x / s) / Real.log (x / s)) t =
      (x / t ^ 2) * (1 - Real.log (x / t)) / (Real.log (x / t)) ^ 2 := by
  obtain ⟨d, hd, hdeq⟩ := hasDerivAt_ratio_log x t htpos hxt
  rw [hd.deriv, hdeq]

/-- Continuity of the closed-form derivative expression. -/
theorem continuousOn_deriv_ratio_log (x : ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hxa : 1 < x / b) (hab : a ≤ b) :
    ContinuousOn (fun t => (x / t ^ 2) * (1 - Real.log (x / t)) / (Real.log (x / t)) ^ 2)
      (Set.Icc a b) := by
  have hxpos : 0 < x := by
    have : 0 < x / b := by linarith
    rcases (div_pos_iff.mp this) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  intro t ht
  simp only [Set.mem_Icc] at ht
  have htpos : 0 < t := lt_of_lt_of_le ha ht.1
  have htne : t ≠ 0 := htpos.ne'
  have hxtpos : 0 < x / t := by positivity
  have hxt : 1 < x / t := by
    have hxb_le : x / b ≤ x / t := by
      apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
    linarith [hxa, hxb_le]
  have hlogne : Real.log (x / t) ≠ 0 := ne_of_gt (Real.log_pos hxt)
  have hcont_xt2 : ContinuousAt (fun s : ℝ => x / s ^ 2) t := by
    apply ContinuousAt.div continuousAt_const
    · exact ContinuousAt.pow continuousAt_id 2
    · exact pow_ne_zero 2 htne
  have hcont_logxt : ContinuousAt (fun s : ℝ => Real.log (x / s)) t := by
    have hdiv_cont : ContinuousAt (fun s : ℝ => x / s) t :=
      ContinuousAt.div continuousAt_const continuousAt_id htne
    exact (Real.continuousAt_log hxtpos.ne').comp hdiv_cont
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · apply ContinuousAt.mul hcont_xt2
    exact ContinuousAt.sub continuousAt_const hcont_logxt
  · exact ContinuousAt.pow hcont_logxt 2
  · exact pow_ne_zero 2 hlogne

/-- IntegrableOn (deriv f) (Icc a b). -/
theorem integrableOn_deriv_ratio_log (x : ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hxa : 1 < x / b) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn (deriv (fun s => (x / s) / Real.log (x / s)))
      (Set.Icc a b) MeasureTheory.volume := by
  have hcont := continuousOn_deriv_ratio_log x a b ha hb hxa hab
  have heq : Set.EqOn (fun t => (x / t ^ 2) * (1 - Real.log (x / t)) / (Real.log (x / t)) ^ 2)
      (deriv (fun s => (x / s) / Real.log (x / s)))
      (Set.Icc a b) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hxpos : 0 < x := by
      have : 0 < x / b := by linarith
      rcases (div_pos_iff.mp this) with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    have hxt : 1 < x / t := by
      have hxb_le : x / b ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
      linarith [hxa, hxb_le]
    exact (deriv_ratio_log_eq x t htpos hxt).symm
  exact hcont.integrableOn_Icc.congr_fun heq measurableSet_Icc

/-- Generalized version with an arbitrary upper bound B. -/
theorem abel_summation_ratio_log_gen (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (hxpos : 0 < x) (B : ℝ) (hB1 : 1 < x / B) (hx3 : (p₀ : ℝ) ≤ B) :
    ∑ k ∈ Finset.Ioc p₀ ⌊B⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) =
      ((x / B) / Real.log (x / B)) * (Nat.primeCounting ⌊B⌋₊ : ℝ) -
      ((x / (p₀:ℝ)) / Real.log (x / (p₀:ℝ))) * (Nat.primeCounting p₀ : ℝ) -
      ∫ t in Set.Ioc (p₀:ℝ) B,
        deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  have hp₀pos : (0:ℝ) ≤ (p₀ : ℝ) := by positivity
  have hb : 0 < B := by
    by_contra hle
    push_neg at hle
    have : x / B ≤ 0 := div_nonpos_of_nonneg_of_nonpos hxpos.le hle
    linarith
  have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hxb : 1 < x / (p₀:ℝ) := by
    have hge : x / (p₀:ℝ) ≥ x / B := by
      apply div_le_div_of_nonneg_left hxpos.le ha hx3
    linarith [hB1]
  have hdiff : ∀ t ∈ Set.Icc (p₀:ℝ) B, DifferentiableAt ℝ
      (fun s => (x / s) / Real.log (x / s)) t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hxt : 1 < x / t := by
      have hge2 : x / B ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
      linarith [hB1]
    exact differentiableAt_ratio_log x t htpos hxt
  have hint := integrableOn_deriv_ratio_log x (p₀:ℝ) B ha hb hB1 (by linarith)
  have habel := sum_mul_eq_sub_sub_integral_mul (fun k => if Nat.Prime k then (1:ℝ) else 0)
    ha.le (by linarith) hdiff hint
  simp only [Nat.floor_natCast] at habel
  have hbridge : ∀ N : ℕ, (∑ k ∈ Finset.Icc 0 N, if Nat.Prime k then (1:ℝ) else 0) =
      (Nat.primeCounting N : ℝ) := by
    intro N
    classical
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [show Finset.Icc 0 N = Finset.range (N+1) by
      ext m; simp [Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]]
    rw [Finset.sum_boole]
  simp_rw [hbridge] at habel
  exact habel

theorem abel_summation_ratio_log (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (hxpos : 0 < x) (hx3 : (p₀ : ℝ) ≤ x / 3) :
    ∑ k ∈ Finset.Ioc p₀ ⌊x / 3⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) =
      ((x / (x/3)) / Real.log (x / (x/3))) * (Nat.primeCounting ⌊x/3⌋₊ : ℝ) -
      ((x / (p₀:ℝ)) / Real.log (x / (p₀:ℝ))) * (Nat.primeCounting p₀ : ℝ) -
      ∫ t in Set.Ioc (p₀:ℝ) (x/3),
        deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  have hp₀pos : (0:ℝ) ≤ (p₀ : ℝ) := by positivity
  have hb : 0 < x / 3 := by linarith
  have hxa : 1 < x / (x/3) := by
    have heq : x / (x/3) = 3 := by field_simp
    rw [heq]; norm_num
  have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hxb : 1 < x / (p₀:ℝ) := by
    have hge : x / (p₀:ℝ) ≥ x / (x/3) := by
      apply div_le_div_of_nonneg_left hxpos.le ha hx3
    linarith [hxa]
  have hdiff : ∀ t ∈ Set.Icc (p₀:ℝ) (x/3), DifferentiableAt ℝ
      (fun s => (x / s) / Real.log (x / s)) t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hxt : 1 < x / t := by
      have hge2 : x / (x/3) ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
      linarith [hxa]
    exact differentiableAt_ratio_log x t htpos hxt
  have hint := integrableOn_deriv_ratio_log x (p₀:ℝ) (x/3) ha hb hxa (by linarith)
  have habel := sum_mul_eq_sub_sub_integral_mul (fun k => if Nat.Prime k then (1:ℝ) else 0)
    ha.le (by linarith) hdiff hint
  simp only [Nat.floor_natCast] at habel
  have hbridge : ∀ N : ℕ, (∑ k ∈ Finset.Icc 0 N, if Nat.Prime k then (1:ℝ) else 0) =
      (Nat.primeCounting N : ℝ) := by
    intro N
    classical
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [show Finset.Icc 0 N = Finset.range (N+1) by
      ext m; simp [Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]]
    rw [Finset.sum_boole]
  simp_rw [hbridge] at habel
  exact habel

/-- Bound on the h(x/3)*π(⌊x/3⌋₊) boundary term. -/
theorem boundary_term_bound (x : ℝ) (hx : 9 ≤ x) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ y : ℝ, 3 ≤ y → (piK 1 y : ℝ) ≤ C * y * (Real.log (Real.log y)) ^ (1 - 1) / Real.log y) :
    ((x / (x/3)) / Real.log (x / (x/3))) * (Nat.primeCounting ⌊x/3⌋₊ : ℝ) ≤
      C * (Real.log 3)⁻¹ * x / Real.log (x/3) := by
  have heq3 : x / (x/3) = 3 := by
    have hxpos : 0 < x := by linarith
    field_simp
  rw [heq3]
  have hx3ge3 : (3:ℝ) ≤ x / 3 := by linarith
  have hpc_bound := hbound (x/3) hx3ge3
  rw [piK_one_eq_primeCounting] at hpc_bound
  norm_num at hpc_bound
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogx3pos : 0 < Real.log (x/3) := by
    apply Real.log_pos; linarith
  have hkey : (C * (x/3) / Real.log (x/3)) * (3 / Real.log 3) =
      C * (Real.log 3)⁻¹ * x / Real.log (x/3) := by
    field_simp
  rw [← hkey, mul_comm (3 / Real.log 3)]
  have hpos3log3 : (0:ℝ) ≤ 3 / Real.log 3 := by positivity
  have hCpos : (0:ℝ) ≤ C * (x/3) / Real.log (x/3) := by positivity
  exact mul_le_mul hpc_bound (le_refl _) hpos3log3 hCpos

/-- Generalized version with an arbitrary upper bound B. -/
theorem integral_term_bound_gen (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀) (hxpos : 0 < x)
    (B : ℝ) (hB1 : 3 ≤ x / B) (hx3 : (p₀ : ℝ) ≤ B) :
    -(∫ t in Set.Ioc (p₀:ℝ) B,
        deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ)) ≤
      (Nat.primeCounting ⌊B⌋₊ : ℝ) *
        (((x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ))) - ((x/B) / Real.log (x/B))) := by
  have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hb : 0 < B := by
    by_contra hle
    push_neg at hle
    have : x / B ≤ 0 := div_nonpos_of_nonneg_of_nonpos hxpos.le hle
    linarith
  have hab : (p₀:ℝ) ≤ B := hx3
  have hpc_mono : ∀ t ∈ Set.Ioc (p₀:ℝ) B, (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      (Nat.primeCounting ⌊B⌋₊ : ℝ) := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have hfloor_le : ⌊t⌋₊ ≤ ⌊B⌋₊ := by
      apply Nat.floor_le_floor
      linarith [ht.2]
    exact_mod_cast Nat.monotone_primeCounting hfloor_le
  have hderiv_neg : ∀ t ∈ Set.Ioc (p₀:ℝ) B,
      deriv (fun s => (x / s) / Real.log (x / s)) t ≤ 0 := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1.le
    have hxt3 : (3:ℝ) ≤ x / t := by
      have hge : x / B ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
      linarith [hB1]
    have hxt : 1 < x / t := by linarith
    rw [deriv_ratio_log_eq x t htpos hxt]
    have hlogxt_gt1 : 1 < Real.log (x/t) := by
      have h3le : Real.log 3 ≤ Real.log (x/t) := Real.log_le_log (by norm_num) hxt3
      have hloge1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have : (1:ℝ) < Real.log 3 := by
        calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hloge1
      linarith
    have hnum_neg : (1:ℝ) - Real.log (x/t) < 0 := by linarith
    have hden_pos : (0:ℝ) < (Real.log (x/t))^2 := by positivity
    have hxt2_pos : (0:ℝ) < x/t^2 := by positivity
    have hprod_neg : x/t^2 * (1 - Real.log (x/t)) < 0 := mul_neg_of_pos_of_neg hxt2_pos hnum_neg
    exact div_nonpos_of_nonpos_of_nonneg hprod_neg.le hden_pos.le
  have hint_ftc : ∫ t in Set.Ioc (p₀:ℝ) B, deriv (fun s => (x / s) / Real.log (x / s)) t =
      ((x/B) / Real.log (x/B)) - ((x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ))) := by
    have hdiff : ∀ t ∈ Set.Icc (p₀:ℝ) B, DifferentiableAt ℝ
        (fun s => (x / s) / Real.log (x / s)) t := by
      intro t ht
      simp only [Set.mem_Icc] at ht
      have htpos : 0 < t := lt_of_lt_of_le ha ht.1
      have hxt : 1 < x / t := by
        have hge : x / B ≤ x / t := by
          apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
        linarith [hB1]
      exact differentiableAt_ratio_log x t htpos hxt
    have hcont : ContinuousOn (fun s => (x / s) / Real.log (x / s)) (Set.Icc (p₀:ℝ) B) :=
      fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
    have hint := integrableOn_deriv_ratio_log x (p₀:ℝ) B ha hb (by linarith [hB1]) hab
    rw [← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => (x / s) / Real.log (x / s))
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have htpos' : 0 < t := lt_of_lt_of_le ha ht.1
      have hxt : 1 < x / t := by
        have hge : x / B ≤ x / t := by
          apply div_le_div_of_nonneg_left hxpos.le htpos' ht.2
        linarith [hB1]
      rw [deriv_ratio_log_eq x t htpos' hxt]
      obtain ⟨d, hd, hdeq⟩ := hasDerivAt_ratio_log x t htpos' hxt
      rwa [hdeq] at hd
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact hint.mono_set Set.Ioc_subset_Icc_self
  have hle := MeasureTheory.setIntegral_mono_on
    (μ := MeasureTheory.volume)
    (f := fun t => deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊B⌋₊ : ℝ))
    (g := fun t => deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ))
    sorry sorry measurableSet_Ioc (by
      intro t ht
      have h1 := hderiv_neg t ht
      have h2 := hpc_mono t ht
      nlinarith [mul_le_mul_of_nonpos_left h2 h1])
  rw [MeasureTheory.integral_mul_const, hint_ftc] at hle
  linarith [hle]

theorem integral_term_bound (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀) (hxpos : 0 < x)
    (hx3 : (p₀ : ℝ) ≤ x / 3) :
    -(∫ t in Set.Ioc (p₀:ℝ) (x/3),
        deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ)) ≤
      (Nat.primeCounting ⌊x/3⌋₊ : ℝ) *
        (((x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ))) - ((x/(x/3)) / Real.log (x/(x/3)))) := by
  have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hb : 0 < x / 3 := by linarith
  have hab : (p₀:ℝ) ≤ x/3 := hx3
  have hpc_mono : ∀ t ∈ Set.Ioc (p₀:ℝ) (x/3), (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      (Nat.primeCounting ⌊x/3⌋₊ : ℝ) := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have hfloor_le : ⌊t⌋₊ ≤ ⌊x/3⌋₊ := by
      apply Nat.floor_le_floor
      linarith [ht.2]
    exact_mod_cast Nat.monotone_primeCounting hfloor_le
  have hderiv_neg : ∀ t ∈ Set.Ioc (p₀:ℝ) (x/3),
      deriv (fun s => (x / s) / Real.log (x / s)) t ≤ 0 := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1.le
    have hxt : 1 < x / t := by
      have hge : x / (x/3) ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
      have heq3 : x / (x/3) = 3 := by field_simp
      linarith [heq3 ▸ hge]
    rw [deriv_ratio_log_eq x t htpos hxt]
    have hxt3 : (3:ℝ) ≤ x / t := by
      have heq3 : x / (x/3) = 3 := by field_simp
      have hge : x / (x/3) ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
      linarith [heq3 ▸ hge]
    have hlogxt_gt1 : 1 < Real.log (x/t) := by
      have h3le : Real.log 3 ≤ Real.log (x/t) := Real.log_le_log (by norm_num) hxt3
      have hloge1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have : (1:ℝ) < Real.log 3 := by
        calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hloge1
      linarith
    have hnum_neg : (1:ℝ) - Real.log (x/t) < 0 := by linarith
    have hden_pos : (0:ℝ) < (Real.log (x/t))^2 := by positivity
    have hxt2_pos : (0:ℝ) < x/t^2 := by positivity
    have hprod_neg : x/t^2 * (1 - Real.log (x/t)) < 0 := mul_neg_of_pos_of_neg hxt2_pos hnum_neg
    exact div_nonpos_of_nonpos_of_nonneg hprod_neg.le hden_pos.le
  have hint_ftc : ∫ t in Set.Ioc (p₀:ℝ) (x/3), deriv (fun s => (x / s) / Real.log (x / s)) t =
      ((x/(x/3)) / Real.log (x/(x/3))) - ((x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ))) := by
    have hdiff : ∀ t ∈ Set.Icc (p₀:ℝ) (x/3), DifferentiableAt ℝ
        (fun s => (x / s) / Real.log (x / s)) t := by
      intro t ht
      simp only [Set.mem_Icc] at ht
      have htpos : 0 < t := lt_of_lt_of_le ha ht.1
      have hxt : 1 < x / t := by
        have heq3 : x / (x/3) = 3 := by field_simp
        have hge : x / (x/3) ≤ x / t := by
          apply div_le_div_of_nonneg_left hxpos.le htpos ht.2
        linarith [heq3 ▸ hge]
      exact differentiableAt_ratio_log x t htpos hxt
    have hcont : ContinuousOn (fun s => (x / s) / Real.log (x / s)) (Set.Icc (p₀:ℝ) (x/3)) :=
      fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
    have hxb : 1 < x / (x/3) := by
      have heq3 : x / (x/3) = 3 := by field_simp
      linarith [heq3]
    have hint := integrableOn_deriv_ratio_log x (p₀:ℝ) (x/3) ha hb hxb hab
    rw [← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => (x / s) / Real.log (x / s))
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have htpos' : 0 < t := lt_of_lt_of_le ha ht.1
      have hxt3 : (3:ℝ) ≤ x / t := by
        have heq3 : x / (x/3) = 3 := by field_simp
        have hge : x / (x/3) ≤ x / t := by
          apply div_le_div_of_nonneg_left hxpos.le htpos' ht.2
        linarith [heq3 ▸ hge]
      have hxt : 1 < x / t := by linarith
      rw [deriv_ratio_log_eq x t htpos' hxt]
      obtain ⟨d, hd, hdeq⟩ := hasDerivAt_ratio_log x t htpos' hxt
      rwa [hdeq] at hd
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact hint.mono_set Set.Ioc_subset_Icc_self
  have hderiv_int : ∫ t in Set.Ioc (p₀:ℝ) (x/3), (-deriv (fun s => (x / s) / Real.log (x / s)) t) =
      ((x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ))) - ((x/(x/3)) / Real.log (x/(x/3))) := by
    rw [MeasureTheory.integral_neg, hint_ftc]; ring
  have hpc_mono' : ∀ t ∈ Set.Ioc (p₀:ℝ) (x/3),
      deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊x/3⌋₊ : ℝ) ≤
      deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    intro t ht
    have h1 := hderiv_neg t ht
    have h2 := hpc_mono t ht
    nlinarith [mul_le_mul_of_nonpos_left h2 h1]
  have hle := MeasureTheory.setIntegral_mono_on
    (μ := MeasureTheory.volume)
    (f := fun t => deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊x/3⌋₊ : ℝ))
    (g := fun t => deriv (fun s => (x / s) / Real.log (x / s)) t * (Nat.primeCounting ⌊t⌋₊ : ℝ))
    sorry sorry measurableSet_Ioc hpc_mono'
  rw [MeasureTheory.integral_mul_const, hint_ftc] at hle
  linarith [hle]

/-- Generalized version with an arbitrary upper bound B. -/
theorem sum_ratio_log_bound_gen (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (hxpos : 0 < x) (B : ℝ) (hB1 : 3 ≤ x / B) (hx3 : (p₀ : ℝ) ≤ B) :
    ∑ k ∈ Finset.Ioc p₀ ⌊B⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
      ((x / (p₀:ℝ)) / Real.log (x / (p₀:ℝ))) * (Nat.primeCounting ⌊B⌋₊ : ℝ) := by
  have habel := abel_summation_ratio_log_gen x p₀ hp₀ hxpos B (by linarith [hB1]) hx3
  have hintbound := integral_term_bound_gen x p₀ hp₀ hxpos B hB1 hx3
  have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hpc_nonneg : (0:ℝ) ≤ (Nat.primeCounting p₀ : ℝ) := by positivity
  have hh_nonneg : (0:ℝ) ≤ (x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ)) := by
    have hxb : 1 < x / (p₀:ℝ) := by
      have hb : 0 < B := by
        by_contra hle
        push_neg at hle
        have : x / B ≤ 0 := div_nonpos_of_nonneg_of_nonpos hxpos.le hle
        linarith
      have hge : x / B ≤ x / (p₀:ℝ) := by
        apply div_le_div_of_nonneg_left hxpos.le ha hx3
      linarith [hB1]
    have hlogpos : 0 < Real.log (x/(p₀:ℝ)) := Real.log_pos hxb
    positivity
  nlinarith [habel, hintbound, mul_nonneg hh_nonneg hpc_nonneg]

theorem sum_ratio_log_bound (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (hxpos : 0 < x) (hx3 : (p₀ : ℝ) ≤ x / 3) :
    ∑ k ∈ Finset.Ioc p₀ ⌊x / 3⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
      ((x / (p₀:ℝ)) / Real.log (x / (p₀:ℝ))) * (Nat.primeCounting ⌊x/3⌋₊ : ℝ) := by
  have habel := abel_summation_ratio_log x p₀ hp₀ hxpos hx3
  have hintbound := integral_term_bound x p₀ hp₀ hxpos hx3
  have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hpc_nonneg : (0:ℝ) ≤ (Nat.primeCounting p₀ : ℝ) := by positivity
  have hh_nonneg : (0:ℝ) ≤ (x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ)) := by
    have hxb : 1 < x / (p₀:ℝ) := by
      have heq3 : x / (x/3) = 3 := by field_simp
      have hge : x / (x/3) ≤ x / (p₀:ℝ) := by
        apply div_le_div_of_nonneg_left hxpos.le ha hx3
      linarith [heq3 ▸ hge]
    have hlogpos : 0 < Real.log (x/(p₀:ℝ)) := Real.log_pos hxb
    positivity
  nlinarith [habel, hintbound, mul_nonneg hh_nonneg hpc_nonneg]

/-- h(p₀) ≤ h(1) = x/logx, since h is antitone on [1,p₀]. -/
theorem h_p0_bound (x : ℝ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀) (hxpos : 0 < x)
    (hx3 : (p₀:ℝ) ≤ x/3) :
    (x/(p₀:ℝ)) / Real.log (x/(p₀:ℝ)) ≤ x / Real.log x := by
  rcases eq_or_lt_of_le hp₀ with heq | hlt
  · simp [← heq]
  · have ha : 0 < (p₀:ℝ) := by exact_mod_cast hp₀
    have h1lt : (1:ℝ) < (p₀:ℝ) := by exact_mod_cast hlt
    have hconv : Convex ℝ (Set.Icc (1:ℝ) (p₀:ℝ)) := convex_Icc _ _
    have hint_eq : interior (Set.Icc (1:ℝ) (p₀:ℝ)) = Set.Ioo (1:ℝ) (p₀:ℝ) :=
      interior_Icc
    have hxt3_of : ∀ t, 1 ≤ t → t ≤ (p₀:ℝ) → (3:ℝ) ≤ x / t := by
      intro t ht1 ht2
      have htle3 : t ≤ x/3 := le_trans ht2 hx3
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      have heq3 : x / (x/3) = 3 := by field_simp
      have hge : x / (x/3) ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos htle3
      linarith [heq3 ▸ hge]
    have hcont : ContinuousOn (fun s => (x/s)/Real.log (x/s)) (Set.Icc (1:ℝ) (p₀:ℝ)) := by
      intro t ht
      simp only [Set.mem_Icc] at ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht.1
      have hxt3 := hxt3_of t ht.1 ht.2
      exact (differentiableAt_ratio_log x t htpos (by linarith)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun s => (x/s)/Real.log (x/s))
        (interior (Set.Icc (1:ℝ) (p₀:ℝ))) := by
      rw [hint_eq]
      intro t ht
      simp only [Set.mem_Ioo] at ht
      have htpos : 0 < t := lt_trans one_pos ht.1
      have hxt3 := hxt3_of t ht.1.le ht.2.le
      exact (differentiableAt_ratio_log x t htpos (by linarith)).differentiableWithinAt
    have hderiv_np : ∀ t ∈ interior (Set.Icc (1:ℝ) (p₀:ℝ)),
        deriv (fun s => (x/s)/Real.log (x/s)) t ≤ 0 := by
      rw [hint_eq]
      intro t ht
      simp only [Set.mem_Ioo] at ht
      have htpos : 0 < t := lt_trans one_pos ht.1
      have hxt3 := hxt3_of t ht.1.le ht.2.le
      have hxt : 1 < x / t := by linarith
      rw [deriv_ratio_log_eq x t htpos hxt]
      have hlogxt_gt1 : 1 < Real.log (x/t) := by
        have h3le : Real.log 3 ≤ Real.log (x/t) := Real.log_le_log (by norm_num) hxt3
        have hloge1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        have hl3 : (1:ℝ) < Real.log 3 := by
          calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hloge1
        linarith
      have hnum_neg : (1:ℝ) - Real.log (x/t) < 0 := by linarith
      have hden_pos : (0:ℝ) < (Real.log (x/t))^2 := by positivity
      have hxt2_pos : (0:ℝ) < x/t^2 := by positivity
      have hprod_neg : x/t^2 * (1 - Real.log (x/t)) < 0 := mul_neg_of_pos_of_neg hxt2_pos hnum_neg
      exact div_nonpos_of_nonpos_of_nonneg hprod_neg.le hden_pos.le
    have hanti := antitoneOn_of_deriv_nonpos hconv hcont hdiff hderiv_np
    have h1mem : (1:ℝ) ∈ Set.Icc (1:ℝ) (p₀:ℝ) := ⟨le_refl _, h1lt.le⟩
    have hpmem : (p₀:ℝ) ∈ Set.Icc (1:ℝ) (p₀:ℝ) := ⟨h1lt.le, le_refl _⟩
    have := hanti h1mem hpmem h1lt.le
    simpa using this

theorem piKFrom_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (x : ℝ), 3 ≤ x →
      (piKFrom k x p₀ : ℝ) ≤ C * x * (Real.log (Real.log x)) ^ (k - 1) / Real.log x := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      obtain ⟨C, hC, hbound⟩ := piK_bound_one
      refine ⟨C, hC, fun p₀ x hx => ?_⟩
      have hsub : piKFrom 1 x p₀ ≤ piK 1 x := by
        unfold piKFrom piK
        apply Finset.card_le_card
        intro n hn
        classical
        obtain ⟨hnmem, hnO, _⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hnmem, hnO⟩
      calc (piKFrom 1 x p₀ : ℝ) ≤ (piK 1 x : ℝ) := by exact_mod_cast hsub
        _ ≤ C * x * (Real.log (Real.log x)) ^ (1 - 1) / Real.log x := hbound x hx
    · obtain ⟨C, hC, hbound⟩ := ih hnpos
      refine ⟨C * 100, by positivity, fun p₀ x hx => ?_⟩
      rw [piKFrom_succ_eq n hnpos x p₀ (by linarith)]
      have hterm_bound : ∀ p ∈ (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime),
          x / p ≥ 3 → (piKFrom n (x / p) p : ℝ) ≤
            C * (x / p) * (Real.log (Real.log (x / p))) ^ (n - 1) / Real.log (x / p) := by
        intro p hp hge3
        exact hbound p (x / p) hge3
      have hloglog_crude : ∀ p : ℝ, p ≥ 1 → x / p ≥ 3 →
          Real.log (Real.log (x / p)) ≤ Real.log (Real.log x) := by
        intro p hp1 hge3
        have hxp_le : x / p ≤ x := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [hx, hp1]
        have hlogxp_pos : 0 < Real.log (x / p) := Real.log_pos (by linarith)
        apply Real.log_le_log hlogxp_pos
        exact Real.log_le_log (by linarith) hxp_le
      have hterm_bound2 : ∀ p ∈ (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime),
          (p:ℝ) ≥ 1 → x / p ≥ 3 → (piKFrom n (x / p) p : ℝ) ≤
            C * (Real.log (Real.log x)) ^ (n - 1) * ((x / p) / Real.log (x / p)) := by
        intro p hp hp1 hge3
        have h1 := hterm_bound p hp hge3
        have h2 := hloglog_crude p hp1 hge3
        have hloglogpos : 0 ≤ Real.log (Real.log (x/p)) := by
          have hxp3 : (3:ℝ) ≤ x/p := hge3
          have he_lt3 : Real.exp 1 < 3 := by
            have := Real.exp_one_lt_d9
            linarith
          have hloge_lt3 : (1:ℝ) < Real.log 3 := by
            calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
              _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he_lt3
          have h3le : Real.log 3 ≤ Real.log (x/p) := Real.log_le_log (by norm_num) hxp3
          have hge1 : (1:ℝ) ≤ Real.log (x/p) := by linarith
          exact Real.log_nonneg hge1
        have hpow_le : (Real.log (Real.log (x/p))) ^ (n-1) ≤ (Real.log (Real.log x)) ^ (n-1) := by
          apply pow_le_pow_left₀ hloglogpos h2
        calc (piKFrom n (x / p) p : ℝ)
            ≤ C * (x / p) * (Real.log (Real.log (x / p))) ^ (n - 1) / Real.log (x / p) := h1
          _ ≤ C * (Real.log (Real.log x)) ^ (n - 1) * ((x / p) / Real.log (x / p)) := by
              rw [show C * (x/p) * (Real.log (Real.log (x/p)))^(n-1) / Real.log (x/p) =
                  C * ((Real.log (Real.log (x/p)))^(n-1)) * ((x/p) / Real.log (x/p)) by ring]
              gcongr
              have hlogxp_pos : 0 < Real.log (x/p) := by
                apply Real.log_pos
                linarith [hge3]
              have hxp_pos : 0 ≤ x/p := by linarith [hge3]
              positivity
      have hvanish2 : ∀ p ∈ (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime),
          n ≥ 2 → x / p < 3 → piKFrom n (x / p) p = 0 := by
        intro p hp hn2 hlt
        classical
        unfold piKFrom
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro m hm
        simp only [Finset.mem_Icc] at hm
        intro hcontra
        obtain ⟨hmO, _⟩ := hcontra
        have hmge : (2:ℝ) ^ n ≤ m := by
          have := pow_bigOmega_le m (by omega)
          rw [hmO] at this
          exact_mod_cast this
        have h4le : (4:ℝ) ≤ 2 ^ n := by
          calc (4:ℝ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
        have hmle : (m:ℝ) ≤ x / p := by
          have h1 : (m:ℝ) ≤ (⌊x/p⌋₊ : ℝ) := by exact_mod_cast hm.2
          have h2 : (⌊x/p⌋₊ : ℝ) ≤ x / p := Nat.floor_le (by positivity)
          linarith
        linarith
      sorry

theorem erdos_sums_increase_from_six
    (hnum : NumericalFacts) :
    ∀ k : ℕ, 6 ≤ k → f k < f (k + 1) := by
  sorry

end
