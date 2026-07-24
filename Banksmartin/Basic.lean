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

theorem erdos_sums_increase_from_six
    (hnum : NumericalFacts) :
    ∀ k : ℕ, 6 ≤ k → f k < f (k + 1) := by
  sorry

end
