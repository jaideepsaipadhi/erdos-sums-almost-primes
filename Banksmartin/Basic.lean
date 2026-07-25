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

/-- The density constant d from Gorodetsky-Lichtman-Wong, "On Erdos sums of
almost primes", C. R. Math. 362 (2024), eq. (1):
d = (1/4) * prod_{p > 2} (1 - 2/p)^(-1) (1 - 1/p)^2 = 0.37869...
Defined as the genuine Euler product (tprod over primes; factors at p = 2
are set to 1). The numerical enclosure is carried by NumericalFacts. -/
noncomputable def dConst : ℝ :=
  (1 / 4) * ∏' p : Nat.Primes,
    (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1)

/-- The secondary-term constant a1 = d * log 2 / 4 from GLW Theorem 2:
f_k = 1 - 2^(-k) (a1 k^2 + O(k log(k+1))). -/
noncomputable def aOneConst : ℝ := dConst * Real.log 2 / 4
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

/-- Decompose a sum over `Ioc p₀ N` into dyadic fibers indexed by `Nat.log 2 k`.
Pure bookkeeping via `Finset.sum_fiberwise_of_maps_to`: fibers of a function are
disjoint for free, so no partition or covering lemma is needed. -/
theorem sum_dyadic_fiberwise (p₀ N : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Ioc p₀ N, g k =
      ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        ∑ k ∈ (Finset.Ioc p₀ N).filter (fun k => Nat.log 2 k = j), g k := by
  classical
  refine (Finset.sum_fiberwise_of_maps_to ?_ g).symm
  intro k hk
  simp only [Finset.mem_Ioc] at hk
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.log_mono_right hk.2

/-- Elements of dyadic fiber `j` satisfy `2^j ≤ k < 2^(j+1)`. -/
theorem dyadic_fiber_mem_bounds (p₀ N j k : ℕ)
    (hk : k ∈ (Finset.Ioc p₀ N).filter (fun k => Nat.log 2 k = j)) :
    2 ^ j ≤ k ∧ k < 2 ^ (j + 1) := by
  classical
  obtain ⟨hkmem, hkj⟩ := Finset.mem_filter.mp hk
  simp only [Finset.mem_Ioc] at hkmem
  have hk0 : k ≠ 0 := by omega
  constructor
  · calc 2 ^ j = 2 ^ Nat.log 2 k := by rw [hkj]
      _ ≤ k := Nat.pow_log_le_self 2 hk0
  · calc k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
      _ = 2 ^ (j + 1) := by rw [hkj]

/-- The number of primes in dyadic fiber `j` is at most pi(2^(j+1)). -/
theorem dyadic_fiber_prime_card (p₀ N j : ℕ) :
    ((((Finset.Ioc p₀ N).filter (fun k => Nat.log 2 k = j)).filter
        (fun k => Nat.Prime k)).card : ℝ) ≤
      (Nat.primeCounting (2 ^ (j + 1)) : ℝ) := by
  classical
  have hsub : (((Finset.Ioc p₀ N).filter (fun k => Nat.log 2 k = j)).filter
      (fun k => Nat.Prime k)) ⊆
      (Finset.range (2 ^ (j + 1) + 1)).filter Nat.Prime := by
    intro k hk
    obtain ⟨hkfib, hkp⟩ := Finset.mem_filter.mp hk
    have hb := dyadic_fiber_mem_bounds p₀ N j k hkfib
    refine Finset.mem_filter.mpr ⟨?_, hkp⟩
    exact Finset.mem_range.mpr (by omega)
  have hcount : Nat.primeCounting (2 ^ (j + 1)) =
      ((Finset.range (2 ^ (j + 1) + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hcard := Finset.card_le_card hsub
  rw [hcount]
  exact_mod_cast hcard

/-- h(t) = (x/t)/log(x/t) is antitone on [1, x/3]. Extracted from the argument
inside `h_p0_bound` so it can be reused per dyadic fiber. -/
theorem ratio_log_antitoneOn (x : ℝ) (hx : 3 ≤ x) :
    AntitoneOn (fun s => (x / s) / Real.log (x / s)) (Set.Icc (1:ℝ) (x / 3)) := by
  have hxpos : (0:ℝ) < x := by linarith
  have hconv : Convex ℝ (Set.Icc (1:ℝ) (x/3)) := convex_Icc _ _
  have hint_eq : interior (Set.Icc (1:ℝ) (x/3)) = Set.Ioo (1:ℝ) (x/3) := interior_Icc
  have hxt3_of : ∀ t, 1 ≤ t → t ≤ x/3 → (3:ℝ) ≤ x / t := by
    intro t ht1 ht2
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have heq3 : x / (x/3) = 3 := by field_simp
    have hge : x / (x/3) ≤ x / t := div_le_div_of_nonneg_left hxpos.le htpos ht2
    linarith [heq3 ▸ hge]
  have hcont : ContinuousOn (fun s => (x/s)/Real.log (x/s)) (Set.Icc (1:ℝ) (x/3)) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht.1
    have hxt3 := hxt3_of t ht.1 ht.2
    exact (differentiableAt_ratio_log x t htpos (by linarith)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (x/s)/Real.log (x/s))
      (interior (Set.Icc (1:ℝ) (x/3))) := by
    rw [hint_eq]
    intro t ht
    simp only [Set.mem_Ioo] at ht
    have htpos : 0 < t := lt_trans one_pos ht.1
    have hxt3 := hxt3_of t ht.1.le ht.2.le
    exact (differentiableAt_ratio_log x t htpos (by linarith)).differentiableWithinAt
  have hderiv_np : ∀ t ∈ interior (Set.Icc (1:ℝ) (x/3)),
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
    have hprod_neg : x/t^2 * (1 - Real.log (x/t)) < 0 :=
      mul_neg_of_pos_of_neg hxt2_pos hnum_neg
    exact div_nonpos_of_nonpos_of_nonneg hprod_neg.le hden_pos.le
  exact antitoneOn_of_deriv_nonpos hconv hcont hdiff hderiv_np

/-- Fiber j = 0 is empty: every k in `Ioc p₀ N` has k ≥ 2, hence `Nat.log 2 k ≥ 1`. -/
theorem dyadic_fiber_zero_empty (p₀ N : ℕ) (hp₀ : 1 ≤ p₀) :
    (Finset.Ioc p₀ N).filter (fun k => Nat.log 2 k = 0) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro k hk
  simp only [Finset.mem_Ioc] at hk
  have h2k : 2 ≤ k := by omega
  have hpos : 0 < Nat.log 2 k := Nat.log_pos (by norm_num) h2k
  omega

/-- Per-fiber bound: on dyadic fiber j, every term is at most h(2^j) (antitone),
and the number of prime terms is at most pi(2^(j+1)). -/
theorem dyadic_fiber_sum_bound (x : ℝ) (p₀ j : ℕ) (hp₀ : 1 ≤ p₀)
    (hx : 9 ≤ x) (h2j : (2 ^ j : ℝ) ≤ x / 3) :
    ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
      ((x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ))) *
        (Nat.primeCounting (2 ^ (j + 1)) : ℝ) := by
  classical
  have hxpos : (0:ℝ) < x := by linarith
  have h2jpos : (0:ℝ) < (2 ^ j : ℝ) := by positivity
  have hx2j3 : (3:ℝ) ≤ x / (2 ^ j : ℝ) := by
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) ≤ x / (2 ^ j : ℝ) :=
      div_le_div_of_nonneg_left hxpos.le h2jpos h2j
    linarith [heq3 ▸ hge]
  have hlogpos : 0 < Real.log (x / (2 ^ j : ℝ)) := Real.log_pos (by linarith)
  have hb_nonneg : 0 ≤ (x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ)) :=
    div_nonneg (div_nonneg hxpos.le h2jpos.le) hlogpos.le
  have h1le2j : (1:ℝ) ≤ (2 ^ j : ℝ) := by
    exact_mod_cast Nat.one_le_two_pow
  have hstep1 : ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
      ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)
      = ∑ k ∈ ((Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j)).filter
          (fun k => Nat.Prime k), ((x / k) / Real.log (x / k)) := by
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hP : Nat.Prime k
    · simp [hP]
    · simp [hP]
  have hanti := ratio_log_antitoneOn x (by linarith)
  have hterm : ∀ k ∈ ((Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j)).filter
      (fun k => Nat.Prime k),
      ((x / k) / Real.log (x / k)) ≤
        ((x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ))) := by
    intro k hk
    obtain ⟨hkS, hkp⟩ := Finset.mem_filter.mp hk
    have hb := dyadic_fiber_mem_bounds p₀ ⌊x / 3⌋₊ j k hkS
    obtain ⟨hkmem, hkj⟩ := Finset.mem_filter.mp hkS
    simp only [Finset.mem_Ioc] at hkmem
    have hk2 : 2 ≤ k := by omega
    have hk1R : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hkfloor : (k : ℝ) ≤ (⌊x / 3⌋₊ : ℝ) := by exact_mod_cast hkmem.2
    have hfloorle : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
    have hkleR : (k : ℝ) ≤ x / 3 := by linarith
    have h2jkR : (2 ^ j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hb.1
    have hmono := hanti (Set.mem_Icc.mpr ⟨h1le2j, h2j⟩)
      (Set.mem_Icc.mpr ⟨hk1R, hkleR⟩) h2jkR
    simpa using hmono
  have hsum_le := Finset.sum_le_card_nsmul
    (((Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j)).filter
      (fun k => Nat.Prime k))
    (fun k => ((x / k) / Real.log (x / k)))
    ((x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ))) hterm
  rw [nsmul_eq_mul] at hsum_le
  have hcard := dyadic_fiber_prime_card p₀ ⌊x / 3⌋₊ j
  calc ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
      ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)
      = ∑ k ∈ ((Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j)).filter
          (fun k => Nat.Prime k), ((x / k) / Real.log (x / k)) := hstep1
    _ ≤ ((((Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j)).filter
          (fun k => Nat.Prime k)).card : ℝ) *
        ((x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ))) := hsum_le
    _ ≤ (Nat.primeCounting (2 ^ (j + 1)) : ℝ) *
        ((x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard hb_nonneg
    _ = ((x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ))) *
        (Nat.primeCounting (2 ^ (j + 1)) : ℝ) := mul_comm _ _


/-- Chebyshev specialized to powers of two: pi(2^(j+1)) ≤ 8*2^(j+1)/(j+1).
The sqrt term is absorbed via sqrt(n)*log(sqrt(n)) ≤ n and log 2 > 1/2. -/
theorem primeCounting_two_pow_bound (j : ℕ) (hj : 1 ≤ j) :
    (Nat.primeCounting (2 ^ (j + 1)) : ℝ) ≤ 8 * 2 ^ (j + 1) / (j + 1) := by
  have hn4 : 4 ≤ 2 ^ (j + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmain := primeCounting_le_bound_own (2 ^ (j + 1)) hn4
  have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) = (2:ℝ) ^ (j + 1) := by norm_cast
  rw [hcast] at hmain
  have h2pos : (0:ℝ) < (2:ℝ) ^ (j + 1) := by positivity
  have hj1pos : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsqrt : Real.log (Real.sqrt ((2:ℝ) ^ (j + 1)))
      = ((j:ℝ) + 1) * Real.log 2 / 2 := by
    rw [Real.log_sqrt h2pos.le, Real.log_pow]
    push_cast
    try ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hterm2 : (2:ℝ) ^ (j + 1) * Real.log 4 / Real.log (Real.sqrt ((2:ℝ) ^ (j + 1)))
      = 4 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1) := by
    rw [hlogsqrt, hlog4]
    have hne1 : ((j:ℝ) + 1) ≠ 0 := hj1pos.ne'
    have hne2 : Real.log 2 ≠ 0 := hlog2pos.ne'
    field_simp
    try ring
  have hs_nonneg : 0 ≤ Real.sqrt ((2:ℝ) ^ (j + 1)) := Real.sqrt_nonneg _
  have hlog2_half : (1:ℝ)/2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hsqrt_bound : Real.sqrt ((2:ℝ) ^ (j + 1))
      ≤ 4 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1) := by
    have hlog_le : Real.log (Real.sqrt ((2:ℝ) ^ (j + 1)))
        ≤ Real.sqrt ((2:ℝ) ^ (j + 1)) := Real.log_le_self hs_nonneg
    have hsq : Real.sqrt ((2:ℝ) ^ (j + 1)) * Real.sqrt ((2:ℝ) ^ (j + 1))
        = (2:ℝ) ^ (j + 1) := Real.mul_self_sqrt h2pos.le
    have hkey : Real.sqrt ((2:ℝ) ^ (j + 1)) * (((j:ℝ) + 1) * Real.log 2 / 2)
        ≤ (2:ℝ) ^ (j + 1) := by
      rw [← hlogsqrt]
      calc Real.sqrt ((2:ℝ) ^ (j + 1)) * Real.log (Real.sqrt ((2:ℝ) ^ (j + 1)))
          ≤ Real.sqrt ((2:ℝ) ^ (j + 1)) * Real.sqrt ((2:ℝ) ^ (j + 1)) :=
            mul_le_mul_of_nonneg_left hlog_le hs_nonneg
        _ = (2:ℝ) ^ (j + 1) := hsq
    rw [le_div_iff₀ hj1pos]
    nlinarith [hkey, hs_nonneg, hj1pos, hlog2_half,
      mul_nonneg (mul_nonneg hs_nonneg hj1pos.le) (sub_nonneg.mpr hlog2_half)]
  rw [hterm2] at hmain
  have h48 : 4 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1) + 4 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1)
      = 8 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1) := by ring
  push_cast
  linarith [hmain, hsqrt_bound, h48]

/-- Per-fiber constant simplification:
h(2^j) * pi(2^(j+1)) ≤ 16*x / ((j+1) * log(x/2^j)). -/
theorem dyadic_term_bound (x : ℝ) (j : ℕ) (hj : 1 ≤ j) (hx : 9 ≤ x)
    (h2j : (2:ℝ) ^ j ≤ x / 3) :
    ((x / (2:ℝ) ^ j) / Real.log (x / (2:ℝ) ^ j)) *
        (Nat.primeCounting (2 ^ (j + 1)) : ℝ) ≤
      16 * x / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := by
  have hxpos : (0:ℝ) < x := by linarith
  have h2jpos : (0:ℝ) < (2:ℝ) ^ j := by positivity
  have hx2j3 : (3:ℝ) ≤ x / (2:ℝ) ^ j := by
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) ≤ x / (2:ℝ) ^ j :=
      div_le_div_of_nonneg_left hxpos.le h2jpos h2j
    linarith [heq3 ▸ hge]
  have hlogpos : (0:ℝ) < Real.log (x / (2:ℝ) ^ j) := Real.log_pos (by linarith)
  have hj1pos : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have hh_nonneg : (0:ℝ) ≤ (x / (2:ℝ) ^ j) / Real.log (x / (2:ℝ) ^ j) :=
    div_nonneg (by positivity) hlogpos.le
  have hpc := primeCounting_two_pow_bound j hj
  push_cast at hpc
  have hid : ((x / (2:ℝ) ^ j) / Real.log (x / (2:ℝ) ^ j)) *
      (8 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1))
      = 16 * x / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := by
    have hne1 : ((j:ℝ) + 1) ≠ 0 := hj1pos.ne'
    have hne2 : Real.log (x / (2:ℝ) ^ j) ≠ 0 := hlogpos.ne'
    have hne3 : (2:ℝ) ^ j ≠ 0 := h2jpos.ne'
    rw [pow_succ]
    field_simp
    try ring
  calc ((x / (2:ℝ) ^ j) / Real.log (x / (2:ℝ) ^ j)) *
      (Nat.primeCounting (2 ^ (j + 1)) : ℝ)
      ≤ ((x / (2:ℝ) ^ j) / Real.log (x / (2:ℝ) ^ j)) *
        (8 * (2:ℝ) ^ (j + 1) / ((j:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hpc hh_nonneg
    _ = 16 * x / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := hid

/-- On the low dyadic range ((2^j)^2 ≤ x): log(x/2^j) ≥ (log x)/2. -/
theorem log_ratio_low (x : ℝ) (j : ℕ) (hx : 9 ≤ x)
    (hsq : ((2:ℝ) ^ j) ^ 2 ≤ x) :
    Real.log x / 2 ≤ Real.log (x / (2:ℝ) ^ j) := by
  have hxpos : (0:ℝ) < x := by linarith
  have h2jpos : (0:ℝ) < (2:ℝ) ^ j := by positivity
  have h2j_le_sqrt : (2:ℝ) ^ j ≤ Real.sqrt x := by
    rw [show ((2:ℝ) ^ j) = Real.sqrt (((2:ℝ) ^ j) ^ 2) by
      rw [Real.sqrt_sq h2jpos.le]]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hdiv : Real.sqrt x ≤ x / (2:ℝ) ^ j := by
    rw [le_div_iff₀ h2jpos]
    calc Real.sqrt x * (2:ℝ) ^ j ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h2j_le_sqrt hsqrt_pos.le
      _ = x := Real.mul_self_sqrt hxpos.le
  calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hxpos.le).symm
    _ ≤ Real.log (x / (2:ℝ) ^ j) := Real.log_le_log hsqrt_pos hdiv

/-- Harmonic sum bound, real form: sum_(i<n) 1/(i+1) ≤ 1 + log n. -/
theorem harmonic_sum_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (1:ℝ) / ((i:ℝ) + 1) ≤ 1 + Real.log n := by
  have heq : ((harmonic n : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, (1:ℝ) / ((i:ℝ) + 1) := by
    unfold harmonic
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div]
  rw [← heq]
  exact harmonic_le_one_add_log n


/-- Flip helper: B ≤ x/3 gives 3 ≤ x/B (dedups a pattern used repeatedly). -/
theorem div_ge_three_of_le_third (x B : ℝ) (hxpos : 0 < x) (hB : 0 < B)
    (h : B ≤ x / 3) : 3 ≤ x / B := by
  have heq3 : x / (x / 3) = 3 := by field_simp
  have hge : x / (x / 3) ≤ x / B := div_le_div_of_nonneg_left hxpos.le hB h
  linarith [heq3 ▸ hge]

/-- For x ≥ 9 we have log x ≥ 2, via e^2 < 7.4 < 9. -/
theorem two_le_log (x : ℝ) (hx : 9 ≤ x) : (2:ℝ) ≤ Real.log x := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have he2 : Real.exp 2 ≤ x := by
    rw [h2]
    nlinarith [(Real.exp_pos 1).le, h1, hx]
  rw [show (2:ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
  exact Real.log_le_log (Real.exp_pos 2) he2

/-- For x ≥ 9, loglog x ≥ log 2. -/
theorem loglog_ge_log_two (x : ℝ) (hx : 9 ≤ x) :
    Real.log 2 ≤ Real.log (Real.log x) := by
  have h2 := two_le_log x hx
  exact Real.log_le_log (by norm_num) (by linarith)

/-- The dyadic index J = Nat.log 2 (floor(x/3)) brackets x/3 between 2^J and 2^(J+1). -/
theorem dyadic_log_bounds (x : ℝ) (hx : 9 ≤ x) :
    (2:ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊) ≤ x / 3 ∧
      x / 3 ≤ (2:ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) := by
  have hx3 : (3:ℝ) ≤ x / 3 := by linarith
  have hN : 3 ≤ ⌊x / 3⌋₊ := Nat.le_floor (by push_cast; linarith)
  constructor
  · have h1 : (2:ℕ) ^ (Nat.log 2 ⌊x / 3⌋₊) ≤ ⌊x / 3⌋₊ :=
      Nat.pow_log_le_self 2 (by omega)
    have h2 : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
    calc (2:ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊)
        = ((2 ^ (Nat.log 2 ⌊x / 3⌋₊) : ℕ) : ℝ) := by norm_cast
      _ ≤ (⌊x / 3⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ x / 3 := h2
  · have h1 : ⌊x / 3⌋₊ < 2 ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : x / 3 < (⌊x / 3⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊x / 3⌋₊ : ℝ) + 1
        ≤ ((2 ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    calc x / 3 ≤ (⌊x / 3⌋₊ : ℝ) + 1 := h2.le
      _ ≤ ((2 ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) : ℕ) : ℝ) := h3
      _ = (2:ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) := by norm_cast

/-- If x/3 ≤ 2^(J+1) then (J+1)*log 2 ≥ (log x)/2, via sqrt x ≤ x/3 for x ≥ 9. -/
theorem log_x_half_le (x : ℝ) (J : ℕ) (hx : 9 ≤ x)
    (hJ : x / 3 ≤ (2:ℝ) ^ (J + 1)) :
    Real.log x / 2 ≤ ((J:ℝ) + 1) * Real.log 2 := by
  have hxpos : (0:ℝ) < x := by linarith
  have h3sqrt : (3:ℝ) ≤ Real.sqrt x := by
    rw [show (3:ℝ) = Real.sqrt 9 by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsqrt_le : Real.sqrt x ≤ x / 3 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    calc Real.sqrt x * 3 ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h3sqrt (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hxpos.le
  calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hxpos.le).symm
    _ ≤ Real.log ((2:ℝ) ^ (J + 1)) :=
        Real.log_le_log (Real.sqrt_pos.mpr hxpos) (le_trans hsqrt_le hJ)
    _ = ((J:ℝ) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        try ring

/-- If 2^J ≤ x then J+1 ≤ 2*log x, for x ≥ 9. -/
theorem J_le_two_log (x : ℝ) (J : ℕ) (hx : 9 ≤ x)
    (hJ : (2:ℝ) ^ J ≤ x) : ((J:ℝ) + 1) ≤ 2 * Real.log x := by
  have hlogx2 := two_le_log x hx
  have hJlog : (J:ℝ) * Real.log 2 ≤ Real.log x := by
    calc (J:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ J) := by rw [Real.log_pow]
      _ ≤ Real.log x := Real.log_le_log (by positivity) hJ
  have hlog2_23 : (2:ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hJle : (J:ℝ) ≤ (3 / 2) * Real.log x := by
    have h1 : (J:ℝ) * ((2:ℝ) / 3) ≤ (J:ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2_23 (by positivity)
    nlinarith [hJlog]
  linarith [hJle, hlogx2]

/-- The final constant absorption: 1 + log(J+1) ≤ 4*loglog x when J+1 ≤ 2*log x. -/
theorem one_add_log_le_loglog (x : ℝ) (J : ℕ) (hx : 9 ≤ x)
    (hJ2 : ((J:ℝ) + 1) ≤ 2 * Real.log x) :
    1 + Real.log ((J:ℝ) + 1) ≤ 4 * Real.log (Real.log x) := by
  have hlogx2 := two_le_log x hx
  have hloglog := loglog_ge_log_two x hx
  have hJ1pos : (0:ℝ) < (J:ℝ) + 1 := by positivity
  have hA : Real.log ((J:ℝ) + 1) ≤ Real.log 2 + Real.log (Real.log x) := by
    calc Real.log ((J:ℝ) + 1) ≤ Real.log (2 * Real.log x) :=
          Real.log_le_log hJ1pos hJ2
      _ = Real.log 2 + Real.log (Real.log x) := Real.log_mul (by norm_num) (by linarith)
  have hB : (1:ℝ) ≤ 2 * Real.log 2 := by
    have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) he
      _ = 2 * Real.log 2 := h4
  linarith [hA, hB, hloglog]

/-- Low dyadic range (j ≤ M, 2M ≤ J): harmonic bound with the (log x)/2 floor. -/
theorem dyadic_low_sum (x : ℝ) (J M : ℕ) (hx : 9 ≤ x) (hM : 2 * M ≤ J)
    (hJ : (2:ℝ) ^ J ≤ x) :
    ∑ j ∈ Finset.range (M + 1), 1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      ≤ 2 / Real.log x * (1 + Real.log ((M:ℝ) + 1)) := by
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx_pos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hc_nonneg : (0:ℝ) ≤ 2 / Real.log x := by positivity
  have hterm : ∀ j ∈ Finset.range (M + 1),
      1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
        ≤ 2 / Real.log x * (1 / ((j:ℝ) + 1)) := by
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hsq : ((2:ℝ) ^ j) ^ 2 ≤ x := by
      have h1 : ((2:ℝ) ^ j) ^ 2 = (2:ℝ) ^ (j * 2) := (pow_mul 2 j 2).symm
      rw [h1]
      calc (2:ℝ) ^ (j * 2) ≤ (2:ℝ) ^ J := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
        _ ≤ x := hJ
    have hlow := log_ratio_low x j hx hsq
    have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
    have hden1 : (0:ℝ) < ((j:ℝ) + 1) * (Real.log x / 2) := by positivity
    have hmono : ((j:ℝ) + 1) * (Real.log x / 2)
        ≤ ((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hlow hj1.le
    have h1 := one_div_le_one_div_of_le hden1 hmono
    have h2 : 1 / (((j:ℝ) + 1) * (Real.log x / 2))
        = 2 / Real.log x * (1 / ((j:ℝ) + 1)) := by
      have hne1 : ((j:ℝ) + 1) ≠ 0 := hj1.ne'
      have hne2 : Real.log x ≠ 0 := hlogx_pos.ne'
      field_simp
      try ring
    calc 1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
        ≤ 1 / (((j:ℝ) + 1) * (Real.log x / 2)) := h1
      _ = 2 / Real.log x * (1 / ((j:ℝ) + 1)) := h2
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : ∑ j ∈ Finset.range (M + 1), 2 / Real.log x * (1 / ((j:ℝ) + 1))
      = 2 / Real.log x * ∑ j ∈ Finset.range (M + 1), (1 / ((j:ℝ) + 1)) := by
    rw [Finset.mul_sum]
  have hharm := harmonic_sum_le (M + 1)
  have hcastlog : Real.log ((M + 1 : ℕ) : ℝ) = Real.log ((M:ℝ) + 1) := by norm_cast
  calc ∑ j ∈ Finset.range (M + 1),
      1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      ≤ ∑ j ∈ Finset.range (M + 1), 2 / Real.log x * (1 / ((j:ℝ) + 1)) := hsum1
    _ = 2 / Real.log x * ∑ j ∈ Finset.range (M + 1), (1 / ((j:ℝ) + 1)) := hsum2
    _ ≤ 2 / Real.log x * (1 + Real.log ((M:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nonneg
        calc ∑ i ∈ Finset.range (M + 1), (1:ℝ) / ((i:ℝ) + 1)
            ≤ 1 + Real.log ((M + 1 : ℕ) : ℝ) := hharm
          _ = 1 + Real.log ((M:ℝ) + 1) := by rw [hcastlog]

/-- High dyadic range (M < j ≤ J, J ≤ 2M+1): reflected harmonic bound. -/
theorem dyadic_high_sum (x : ℝ) (J M : ℕ) (hx : 9 ≤ x) (hJM : J ≤ 2 * M + 1)
    (hJ3 : (2:ℝ) ^ J ≤ x / 3) :
    ∑ j ∈ Finset.Ico (M + 1) (J + 1),
        1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      ≤ 2 / (((J:ℝ) + 1) * Real.log 2) * (1 + Real.log ((J:ℝ) + 1)) := by
  have hxpos : (0:ℝ) < x := by linarith
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hJ1pos : (0:ℝ) < (J:ℝ) + 1 := by positivity
  have hc_nonneg : (0:ℝ) ≤ 2 / (((J:ℝ) + 1) * Real.log 2) := by positivity
  have hterm : ∀ j ∈ Finset.Ico (M + 1) (J + 1),
      1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
        ≤ 2 / (((J:ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hjJ : j ≤ J := by omega
    have h2jpos : (0:ℝ) < (2:ℝ) ^ j := by positivity
    have h2Jpos : (0:ℝ) < (2:ℝ) ^ J := by positivity
    have hx2J : (3:ℝ) ≤ x / (2:ℝ) ^ J :=
      div_ge_three_of_le_third x ((2:ℝ) ^ J) hxpos h2Jpos hJ3
    have hsplit : x / (2:ℝ) ^ j = (x / (2:ℝ) ^ J) * (2:ℝ) ^ (J - j) := by
      have hpow : (2:ℝ) ^ J = (2:ℝ) ^ j * (2:ℝ) ^ (J - j) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
      try ring
    have hx2j_ge : (2:ℝ) ^ ((J - j) + 1) ≤ x / (2:ℝ) ^ j := by
      rw [hsplit, pow_succ]
      have h2 : (2:ℝ) ≤ x / (2:ℝ) ^ J := by linarith
      calc (2:ℝ) ^ (J - j) * 2 ≤ (2:ℝ) ^ (J - j) * (x / (2:ℝ) ^ J) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (x / (2:ℝ) ^ J) * (2:ℝ) ^ (J - j) := mul_comm _ _
    have hlog_ge : ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2
        ≤ Real.log (x / (2:ℝ) ^ j) := by
      have h1 : Real.log ((2:ℝ) ^ ((J - j) + 1))
          = ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        try ring
      calc ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2
          = Real.log ((2:ℝ) ^ ((J - j) + 1)) := h1.symm
        _ ≤ Real.log (x / (2:ℝ) ^ j) := Real.log_le_log (by positivity) hx2j_ge
    have hfrac : ((J:ℝ) + 1) / 2 ≤ (j:ℝ) + 1 := by
      have hn : J + 1 ≤ 2 * (j + 1) := by omega
      have hcast := (Nat.cast_le (α := ℝ)).mpr hn
      push_cast at hcast
      linarith
    have hlog_pos_j : (0:ℝ) < Real.log (x / (2:ℝ) ^ j) := by
      have h1 : (0:ℝ) < ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2 := by positivity
      linarith [hlog_ge]
    have hden_lower : (0:ℝ) <
        ((J:ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2) := by
      positivity
    have hden_ge : ((J:ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2)
        ≤ ((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j) :=
      mul_le_mul hfrac hlog_ge (by positivity) (by positivity)
    have h1 := one_div_le_one_div_of_le hden_lower hden_ge
    have h2 : 1 / (((J:ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2))
        = 2 / (((J:ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := by
      have hne1 : ((J:ℝ) + 1) ≠ 0 := hJ1pos.ne'
      have hne2 : Real.log 2 ≠ 0 := hlog2_pos.ne'
      have hne3 : ((((J - j : ℕ) : ℝ)) + 1) ≠ 0 := by positivity
      field_simp
      try ring
    calc 1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
        ≤ 1 / (((J:ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2)) := h1
      _ = 2 / (((J:ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := h2
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : ∑ j ∈ Finset.Ico (M + 1) (J + 1),
      2 / (((J:ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1))
      = 2 / (((J:ℝ) + 1) * Real.log 2) *
        ∑ j ∈ Finset.Ico (M + 1) (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1)) := by
    rw [Finset.mul_sum]
  have hsub : Finset.Ico (M + 1) (J + 1) ⊆ Finset.range (J + 1) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl
  have hsum3 : ∑ j ∈ Finset.Ico (M + 1) (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1))
      ≤ ∑ j ∈ Finset.range (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  have hreflect : ∑ j ∈ Finset.range (J + 1),
      (1:ℝ) / (((J - j : ℕ) : ℝ) + 1)
      = ∑ i ∈ Finset.range (J + 1), (1:ℝ) / ((i:ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun i => (1:ℝ) / ((i:ℝ) + 1)) (J + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjj : J + 1 - 1 - j = J - j := by omega
    rw [hjj]
  have hharm := harmonic_sum_le (J + 1)
  have hcastlog : Real.log ((J + 1 : ℕ) : ℝ) = Real.log ((J:ℝ) + 1) := by norm_cast
  calc ∑ j ∈ Finset.Ico (M + 1) (J + 1),
      1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      ≤ ∑ j ∈ Finset.Ico (M + 1) (J + 1),
        2 / (((J:ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := hsum1
    _ = 2 / (((J:ℝ) + 1) * Real.log 2) *
        ∑ j ∈ Finset.Ico (M + 1) (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1)) := hsum2
    _ ≤ 2 / (((J:ℝ) + 1) * Real.log 2) *
        ∑ j ∈ Finset.range (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum3 hc_nonneg
    _ = 2 / (((J:ℝ) + 1) * Real.log 2) *
        ∑ i ∈ Finset.range (J + 1), (1 / ((i:ℝ) + 1)) := by rw [hreflect]
    _ ≤ 2 / (((J:ℝ) + 1) * Real.log 2) * (1 + Real.log ((J:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nonneg
        calc ∑ i ∈ Finset.range (J + 1), (1:ℝ) / ((i:ℝ) + 1)
            ≤ 1 + Real.log ((J + 1 : ℕ) : ℝ) := hharm
          _ = 1 + Real.log ((J:ℝ) + 1) := by rw [hcastlog]


/-- Core of the dyadic bound, parametrized by the bracketing index J:
if 2^J ≤ x/3 ≤ 2^(J+1), the fiberwise double sum is at most 384*x*loglog x/log x. -/
theorem sum_ratio_log_dyadic_core (x : ℝ) (p₀ J : ℕ) (hp₀ : 1 ≤ p₀)
    (hx : 9 ≤ x) (h2J3 : (2:ℝ) ^ J ≤ x / 3)
    (hJ13 : x / 3 ≤ (2:ℝ) ^ (J + 1)) :
    ∑ j ∈ Finset.range (J + 1),
        ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
      384 * x * Real.log (Real.log x) / Real.log x := by
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx2 := two_le_log x hx
  have hlogx_pos : (0:ℝ) < Real.log x := by linarith
  have hloglog_pos : (0:ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
  have h2J : (2:ℝ) ^ J ≤ x := by linarith
  have hterm : ∀ j ∈ Finset.range (J + 1),
      ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
        16 * x / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := by
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have h2j : (2:ℝ) ^ j ≤ x / 3 := by
      calc (2:ℝ) ^ j ≤ (2:ℝ) ^ J := by
            apply pow_le_pow_right₀ (by norm_num)
            exact hj
        _ ≤ x / 3 := h2J3
    have hx2j3 : (3:ℝ) ≤ x / (2:ℝ) ^ j :=
      div_ge_three_of_le_third x ((2:ℝ) ^ j) hxpos (by positivity) h2j
    have hlogj_pos : (0:ℝ) < Real.log (x / (2:ℝ) ^ j) := Real.log_pos (by linarith)
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [dyadic_fiber_zero_empty p₀ ⌊x / 3⌋₊ hp₀, Finset.sum_empty]
      have hden : (0:ℝ) < (((0:ℕ):ℝ) + 1) * Real.log (x / (2:ℝ) ^ (0:ℕ)) :=
        mul_pos (by positivity) hlogj_pos
      exact div_nonneg (by linarith) hden.le
    · exact le_trans (dyadic_fiber_sum_bound x p₀ j hp₀ hx h2j)
        (dyadic_term_bound x j hjpos hx h2j)
  have hsum1 := Finset.sum_le_sum hterm
  have hfactor : ∑ j ∈ Finset.range (J + 1),
      16 * x / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      = 16 * x * ∑ j ∈ Finset.range (J + 1),
          1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsplit : ∑ j ∈ Finset.range (J + 1),
      (1:ℝ) / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      = (∑ j ∈ Finset.range (J / 2 + 1),
          (1:ℝ) / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)))
        + ∑ j ∈ Finset.Ico (J / 2 + 1) (J + 1),
            (1:ℝ) / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (J / 2 + 1)) (by omega)).symm
  have hlow := dyadic_low_sum x J (J / 2) hx (by omega) h2J
  have hhigh := dyadic_high_sum x J (J / 2) hx (by omega) h2J3
  have hhalf := log_x_half_le x J hx hJ13
  have hJ2 := J_le_two_log x J hx h2J
  have habs := one_add_log_le_loglog x J hx hJ2
  have hM_log : 1 + Real.log (((J / 2 : ℕ):ℝ) + 1) ≤ 4 * Real.log (Real.log x) := by
    have hle : (J / 2 : ℕ) ≤ J := Nat.div_le_self J 2
    have h1 : (((J / 2 : ℕ):ℝ) + 1) ≤ ((J:ℝ) + 1) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hle
      linarith
    have h2 : Real.log (((J / 2 : ℕ):ℝ) + 1) ≤ Real.log ((J:ℝ) + 1) :=
      Real.log_le_log (by positivity) h1
    linarith [habs]
  have hhigh_coef : 2 / (((J:ℝ) + 1) * Real.log 2) ≤ 4 / Real.log x := by
    have hlogx_ne : Real.log x ≠ 0 := hlogx_pos.ne'
    have h1 : 2 / (((J:ℝ) + 1) * Real.log 2) ≤ 2 / (Real.log x / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hhalf
    have h2 : 2 / (Real.log x / 2) = 4 / Real.log x := by
      field_simp
      try ring
    calc 2 / (((J:ℝ) + 1) * Real.log 2) ≤ 2 / (Real.log x / 2) := h1
      _ = 4 / Real.log x := h2
  have hc_low : (0:ℝ) ≤ 2 / Real.log x := div_nonneg (by norm_num) hlogx_pos.le
  have hL2 : 2 / Real.log x * (1 + Real.log (((J / 2 : ℕ):ℝ) + 1))
      ≤ 8 * Real.log (Real.log x) / Real.log x := by
    calc 2 / Real.log x * (1 + Real.log (((J / 2 : ℕ):ℝ) + 1))
        ≤ 2 / Real.log x * (4 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_left hM_log hc_low
      _ = 8 * Real.log (Real.log x) / Real.log x := by ring
  have hH2 : 2 / (((J:ℝ) + 1) * Real.log 2) * (1 + Real.log ((J:ℝ) + 1))
      ≤ 16 * Real.log (Real.log x) / Real.log x := by
    have h1pl : (0:ℝ) ≤ 1 + Real.log ((J:ℝ) + 1) := by
      have hln : (0:ℝ) ≤ Real.log ((J:ℝ) + 1) :=
        Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg J))
      linarith
    calc 2 / (((J:ℝ) + 1) * Real.log 2) * (1 + Real.log ((J:ℝ) + 1))
        ≤ 4 / Real.log x * (1 + Real.log ((J:ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hhigh_coef h1pl
      _ ≤ 4 / Real.log x * (4 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_left habs (div_nonneg (by norm_num) hlogx_pos.le)
      _ = 16 * Real.log (Real.log x) / Real.log x := by ring
  have hU : ∑ j ∈ Finset.range (J + 1),
      (1:ℝ) / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j))
      ≤ 24 * Real.log (Real.log x) / Real.log x := by
    have h824 : 8 * Real.log (Real.log x) / Real.log x
        + 16 * Real.log (Real.log x) / Real.log x
        = 24 * Real.log (Real.log x) / Real.log x := by ring
    linarith [hsplit, hlow, hhigh, hL2, hH2, h824]
  calc ∑ j ∈ Finset.range (J + 1),
      ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)
      ≤ ∑ j ∈ Finset.range (J + 1),
        16 * x / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := hsum1
    _ = 16 * x * ∑ j ∈ Finset.range (J + 1),
        1 / (((j:ℝ) + 1) * Real.log (x / (2:ℝ) ^ j)) := hfactor
    _ ≤ 16 * x * (24 * Real.log (Real.log x) / Real.log x) :=
        mul_le_mul_of_nonneg_left hU (by linarith)
    _ = 384 * x * Real.log (Real.log x) / Real.log x := by ring

/-- THE dyadic sum bound, now proven: the weighted prime sum
∑_(p prime ≤ x/3) (x/p)/log(x/p) is at most 384*x*loglog x/log x. -/
theorem sum_ratio_log_dyadic :
    ∃ K : ℝ, 0 < K ∧ ∀ (p₀ : ℕ) (x : ℝ), 1 ≤ p₀ → 9 ≤ x →
      ∑ k ∈ Finset.Ioc p₀ ⌊x / 3⌋₊,
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
        K * x * Real.log (Real.log x) / Real.log x := by
  refine ⟨384, by norm_num, fun p₀ x hp₀ hx => ?_⟩
  obtain ⟨h2J3, hJ13⟩ := dyadic_log_bounds x hx
  calc ∑ k ∈ Finset.Ioc p₀ ⌊x / 3⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)
      = ∑ j ∈ Finset.range (Nat.log 2 ⌊x / 3⌋₊ + 1),
          ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
            ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) :=
        sum_dyadic_fiberwise p₀ ⌊x / 3⌋₊ _
    _ ≤ 384 * x * Real.log (Real.log x) / Real.log x :=
        sum_ratio_log_dyadic_core x p₀ (Nat.log 2 ⌊x / 3⌋₊) hp₀ hx h2J3 hJ13

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

/-- Explicit-constant Ioc form of the dyadic bound, for direct use downstream
(the existential master would hide the witness after destructuring). -/
theorem sum_ratio_log_dyadic' (p₀ : ℕ) (x : ℝ) (hp₀ : 1 ≤ p₀) (hx : 9 ≤ x) :
    ∑ k ∈ Finset.Ioc p₀ ⌊x / 3⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
      384 * x * Real.log (Real.log x) / Real.log x := by
  obtain ⟨h2J3, hJ13⟩ := dyadic_log_bounds x hx
  calc ∑ k ∈ Finset.Ioc p₀ ⌊x / 3⌋₊,
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)
      = ∑ j ∈ Finset.range (Nat.log 2 ⌊x / 3⌋₊ + 1),
          ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
            ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) :=
        sum_dyadic_fiberwise p₀ ⌊x / 3⌋₊ _
    _ ≤ 384 * x * Real.log (Real.log x) / Real.log x :=
        sum_ratio_log_dyadic_core x p₀ (Nat.log 2 ⌊x / 3⌋₊) hp₀ hx h2J3 hJ13

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
      refine ⟨(C + 1) * 2000, by nlinarith [hC], fun p₀ x hx => ?_⟩
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
      simp only [Nat.add_sub_cancel]
      have hxpos0 : (0:ℝ) < x := by linarith
      have hdich : 9 ≤ x ∨ x < 9 := by
        by_cases h : (9:ℝ) ≤ x
        · exact Or.inl h
        · exact Or.inr (not_le.mp h)
      rcases hdich with hx9 | hx9
      · -- MAIN BRANCH: x >= 9, thread through the dyadic bound
        push_cast
        classical
        have hlogx_pos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
        have hloglog_pos : (0:ℝ) < Real.log (Real.log x) := by
          have h2 := two_le_log x hx9
          exact Real.log_pos (by linarith)
        have hvanish3 : ∀ p ∈ (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime),
            x / p < 3 → piKFrom n (x / p) p = 0 := by
          intro p hp hlt
          rcases Nat.lt_or_ge n 2 with hn1 | hn2
          · have hn1' : n = 1 := by omega
            subst hn1'
            obtain ⟨hpmem, hpprime⟩ := Finset.mem_filter.mp hp
            have hp2le : 2 ≤ p := hpprime.two_le
            have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
            unfold piKFrom
            apply Finset.card_eq_zero.mpr
            apply Finset.filter_eq_empty_iff.mpr
            intro m hm
            simp only [Finset.mem_Icc] at hm
            intro hcontra
            obtain ⟨hmO, hmin_⟩ := hcontra
            have hmprime : m.Prime := (bigOmega_eq_one_iff m).mp hmO
            have hpm : p ≤ m := hmin_ m hmprime dvd_rfl
            have hmle : (m:ℝ) ≤ x / p := by
              have h1 : (m:ℝ) ≤ (⌊x / p⌋₊ : ℝ) := by exact_mod_cast hm.2
              have h2 : (⌊x / p⌋₊ : ℝ) ≤ x / p :=
                Nat.floor_le (div_nonneg (by linarith) hppos.le)
              linarith
            have hm3 : m < 3 := by
              have hmr : (m:ℝ) < 3 := lt_of_le_of_lt hmle hlt
              exact_mod_cast hmr
            have hp2 : p = 2 := by omega
            rw [hp2] at hlt
            have h2c : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [h2c] at hlt
            linarith
          · exact hvanish2 p hp hn2 hlt
        have hdrop : ∑ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
              (fun p => p ≤ ⌊x / 3⌋₊), (piKFrom n (x / p) p : ℝ)
            = ∑ p ∈ (Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime),
              (piKFrom n (x / p) p : ℝ) := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro p hp hpn
          have hple : ¬ p ≤ ⌊x / 3⌋₊ := fun hle =>
            hpn (Finset.mem_filter.mpr ⟨hp, hle⟩)
          have hgt : ⌊x / 3⌋₊ < p := by omega
          obtain ⟨hpmem, hpprime⟩ := Finset.mem_filter.mp hp
          have hp2le : 2 ≤ p := hpprime.two_le
          have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
          have hxp3 : x / (p:ℝ) < 3 := by
            have h3 : (⌊x / 3⌋₊ : ℝ) + 1 ≤ (p:ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt hgt
            have h2 : x / 3 < (⌊x / 3⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
            rw [div_lt_iff₀ hppos]
            nlinarith [h3, h2]
          rw [hvanish3 p hp hxp3]
          norm_num
        rw [← hdrop]
        have hterm3 : ∀ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
            (fun p => p ≤ ⌊x / 3⌋₊),
            (piKFrom n (x / p) p : ℝ) ≤
              C * (Real.log (Real.log x)) ^ (n - 1) *
                (((x / p) / Real.log (x / p)) * (if Nat.Prime p then 1 else 0 : ℝ)) := by
          intro p hpT
          have hp := Finset.mem_of_mem_filter p hpT
          obtain ⟨_, hple⟩ := Finset.mem_filter.mp hpT
          obtain ⟨hpmem, hpprime⟩ := Finset.mem_filter.mp hp
          have hp2le : 2 ≤ p := hpprime.two_le
          have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
          have hpleR : (p:ℝ) ≤ x / 3 := by
            have h1 : (p:ℝ) ≤ (⌊x / 3⌋₊ : ℝ) := by exact_mod_cast hple
            have h2 : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
            linarith
          have hge3 : x / (p:ℝ) ≥ 3 :=
            div_ge_three_of_le_third x (p:ℝ) (by linarith) hppos hpleR
          have hp1R : (1:ℝ) ≤ (p:ℝ) := by
            have h2r : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2le
            linarith
          have h1 := hterm_bound2 p hp hp1R hge3
          rw [if_pos hpprime, mul_one]
          exact h1
        have hsum2 := Finset.sum_le_sum hterm3
        have hfac : ∑ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
              (fun p => p ≤ ⌊x / 3⌋₊),
              C * (Real.log (Real.log x)) ^ (n - 1) *
                (((x / p) / Real.log (x / p)) * (if Nat.Prime p then 1 else 0 : ℝ))
            = C * (Real.log (Real.log x)) ^ (n - 1) *
              ∑ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
                (fun p => p ≤ ⌊x / 3⌋₊),
                (((x / p) / Real.log (x / p)) * (if Nat.Prime p then 1 else 0 : ℝ)) := by
          rw [Finset.mul_sum]
        have hTsub : ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
            (fun p => p ≤ ⌊x / 3⌋₊) ⊆ Finset.Ioc 1 ⌊x / 3⌋₊ := by
          intro p hpT
          have hp := Finset.mem_of_mem_filter p hpT
          obtain ⟨_, hple⟩ := Finset.mem_filter.mp hpT
          obtain ⟨hpmem, hpprime⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_Ioc.mpr ⟨hpprime.one_lt, hple⟩
        have hnonneg : ∀ k ∈ Finset.Ioc 1 ⌊x / 3⌋₊,
            k ∉ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
              (fun p => p ≤ ⌊x / 3⌋₊) →
            0 ≤ ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) := by
          intro k hk _
          simp only [Finset.mem_Ioc] at hk
          have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
          have hkleR : (k:ℝ) ≤ x / 3 := by
            have h1 : (k:ℝ) ≤ (⌊x / 3⌋₊ : ℝ) := by exact_mod_cast hk.2
            have h2 : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
            linarith
          have hge3 : (3:ℝ) ≤ x / (k:ℝ) :=
            div_ge_three_of_le_third x (k:ℝ) (by linarith) hkpos hkleR
          have hlogk : (0:ℝ) < Real.log (x / (k:ℝ)) := Real.log_pos (by linarith)
          apply mul_nonneg
          · exact div_nonneg (by linarith) hlogk.le
          · split_ifs <;> norm_num
        have hsum3 := Finset.sum_le_sum_of_subset_of_nonneg hTsub hnonneg
        have hdy := sum_ratio_log_dyadic' 1 x (le_refl 1) hx9
        have hLL_nonneg : (0:ℝ) ≤ Real.log (Real.log x) := hloglog_pos.le
        have hCL_nonneg : (0:ℝ) ≤ C * (Real.log (Real.log x)) ^ (n - 1) :=
          mul_nonneg hC.le (pow_nonneg hLL_nonneg _)
        have hpow : (Real.log (Real.log x)) ^ (n - 1) * Real.log (Real.log x)
            = (Real.log (Real.log x)) ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        have hfinal_eq : C * (Real.log (Real.log x)) ^ (n - 1) *
              (384 * x * Real.log (Real.log x) / Real.log x)
            = 384 * C * x * (Real.log (Real.log x)) ^ n / Real.log x := by
          rw [← hpow]
          ring
        have hcc : 384 * C * x * (Real.log (Real.log x)) ^ n / Real.log x ≤
            (C + 1) * 2000 * x * (Real.log (Real.log x)) ^ n / Real.log x := by
          have hq : (0:ℝ) ≤ x * (Real.log (Real.log x)) ^ n / Real.log x :=
            div_nonneg (mul_nonneg (by linarith) (pow_nonneg hLL_nonneg n)) hlogx_pos.le
          have hs1 : 384 * C * x * (Real.log (Real.log x)) ^ n / Real.log x
              = (384 * C) * (x * (Real.log (Real.log x)) ^ n / Real.log x) := by ring
          have hs2 : (C + 1) * 2000 * x * (Real.log (Real.log x)) ^ n / Real.log x
              = ((C + 1) * 2000) * (x * (Real.log (Real.log x)) ^ n / Real.log x) := by ring
          rw [hs1, hs2]
          apply mul_le_mul_of_nonneg_right _ hq
          linarith
        calc ∑ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
              (fun p => p ≤ ⌊x / 3⌋₊), (piKFrom n (x / p) p : ℝ)
            ≤ ∑ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
              (fun p => p ≤ ⌊x / 3⌋₊),
              C * (Real.log (Real.log x)) ^ (n - 1) *
                (((x / p) / Real.log (x / p)) * (if Nat.Prime p then 1 else 0 : ℝ)) := hsum2
          _ = C * (Real.log (Real.log x)) ^ (n - 1) *
              ∑ p ∈ ((Finset.Icc p₀ ⌊x⌋₊).filter (fun p => p.Prime)).filter
                (fun p => p ≤ ⌊x / 3⌋₊),
                (((x / p) / Real.log (x / p)) * (if Nat.Prime p then 1 else 0 : ℝ)) := hfac
          _ ≤ C * (Real.log (Real.log x)) ^ (n - 1) *
              ∑ k ∈ Finset.Ioc 1 ⌊x / 3⌋₊,
                (((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)) :=
              mul_le_mul_of_nonneg_left hsum3 hCL_nonneg
          _ ≤ C * (Real.log (Real.log x)) ^ (n - 1) *
              (384 * x * Real.log (Real.log x) / Real.log x) :=
              mul_le_mul_of_nonneg_left hdy hCL_nonneg
          _ = 384 * C * x * (Real.log (Real.log x)) ^ n / Real.log x := hfinal_eq
          _ ≤ (C + 1) * 2000 * x * (Real.log (Real.log x)) ^ n / Real.log x := hcc
      · -- SMALL BRANCH: 3 <= x < 9
        rw [← piKFrom_succ_eq n hnpos x p₀ (by linarith)]
        classical
        have hlog3_ge : (27:ℝ)/25 ≤ Real.log 3 := by
          have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          have h1 : (23:ℝ)/25 ≤ Real.exp (-((2:ℝ)/25)) := by
            have := Real.add_one_le_exp (-((2:ℝ)/25))
            linarith
          have hmul : Real.exp ((2:ℝ)/25) * Real.exp (-((2:ℝ)/25)) = 1 := by
            rw [← Real.exp_add]
            simp
          have h2 : Real.exp ((2:ℝ)/25) ≤ 25/23 := by
            have hepos : (0:ℝ) < Real.exp (-((2:ℝ)/25)) := Real.exp_pos _
            nlinarith [hmul, h1, hepos, (Real.exp_pos ((2:ℝ)/25)).le]
          have h4 : Real.exp ((27:ℝ)/25) ≤ 3 := by
            have hsplit : Real.exp ((27:ℝ)/25) = Real.exp 1 * Real.exp ((2:ℝ)/25) := by
              rw [← Real.exp_add]
              norm_num
            rw [hsplit]
            nlinarith [he, h2, (Real.exp_pos ((2:ℝ)/25)).le, (Real.exp_pos 1).le]
          have h5 : Real.log (Real.exp ((27:ℝ)/25)) ≤ Real.log 3 :=
            Real.log_le_log (Real.exp_pos _) h4
          rwa [Real.log_exp] at h5
        have hlogx_ge : (27:ℝ)/25 ≤ Real.log x :=
          le_trans hlog3_ge (Real.log_le_log (by norm_num) hx)
        have hlx_pos : (0:ℝ) < Real.log x := by linarith
        have hlog3_le : Real.log 3 ≤ (9:ℝ)/8 := by
          have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
          have h1 : (9:ℝ)/8 ≤ Real.exp ((1:ℝ)/8) := by
            have := Real.add_one_le_exp ((1:ℝ)/8)
            linarith
          have h2 : (3:ℝ) ≤ Real.exp ((9:ℝ)/8) := by
            have hsplit : Real.exp ((9:ℝ)/8) = Real.exp 1 * Real.exp ((1:ℝ)/8) := by
              rw [← Real.exp_add]
              norm_num
            rw [hsplit]
            nlinarith [he, h1, (Real.exp_pos ((1:ℝ)/8)).le, (Real.exp_pos 1).le]
          have h5 : Real.log 3 ≤ Real.log (Real.exp ((9:ℝ)/8)) :=
            Real.log_le_log (by norm_num) h2
          rwa [Real.log_exp] at h5
        have hlogx_le : Real.log x ≤ (9:ℝ)/4 := by
          have h1 : Real.log x ≤ Real.log 9 := Real.log_le_log (by linarith) (by linarith)
          have h2 : Real.log 9 = 2 * Real.log 3 := by
            rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
            norm_num
          linarith [hlog3_le]
        have hLL_ge : (2:ℝ)/27 ≤ Real.log (Real.log x) := by
          have h1 : Real.log ((Real.log x)⁻¹) ≤ (Real.log x)⁻¹ - 1 :=
            Real.log_le_sub_one_of_pos (inv_pos.mpr hlx_pos)
          rw [Real.log_inv] at h1
          have h3 : 1 / Real.log x ≤ 1 / ((27:ℝ)/25) :=
            one_div_le_one_div_of_le (by norm_num) hlogx_ge
          simp only [one_div] at h3
          have h4 : ((27:ℝ)/25)⁻¹ = 25/27 := by norm_num
          rw [h4] at h3
          linarith [h1, h3]
        rcases Nat.lt_or_ge n 3 with hn3 | hn3
        · -- n <= 2: numeric absorption
          have hn2' : n ≤ 2 := by omega
          have hLLn : (4:ℝ)/729 ≤ (Real.log (Real.log x)) ^ n := by
            calc (4:ℝ)/729 = ((2:ℝ)/27) ^ 2 := by norm_num
              _ ≤ ((2:ℝ)/27) ^ n := by
                  apply pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2'
              _ ≤ (Real.log (Real.log x)) ^ n := by
                  apply pow_le_pow_left₀ (by norm_num) hLL_ge
          have hcount : (piKFrom (n + 1) x p₀ : ℝ) ≤ x := by
            have h1 : piKFrom (n + 1) x p₀ ≤ (Finset.Icc 2 ⌊x⌋₊).card := by
              unfold piKFrom
              exact Finset.card_filter_le _ _
            have h2 : (Finset.Icc 2 ⌊x⌋₊).card ≤ ⌊x⌋₊ := by
              rw [Nat.card_Icc]
              omega
            have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
            calc (piKFrom (n + 1) x p₀ : ℝ)
                ≤ ((Finset.Icc 2 ⌊x⌋₊).card : ℝ) := by exact_mod_cast h1
              _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h2
              _ ≤ x := h3
          have hinv : (4:ℝ)/9 ≤ 1 / Real.log x := by
            calc (4:ℝ)/9 = 1 / ((9:ℝ)/4) := by norm_num
              _ ≤ 1 / Real.log x := one_div_le_one_div_of_le hlx_pos hlogx_le
          have hs1 : (6000:ℝ) ≤ (C + 1) * 2000 * x := by
            nlinarith [mul_nonneg hC.le (by linarith : (0:ℝ) ≤ x)]
          have hs2 : (6000:ℝ) * ((4:ℝ)/729)
              ≤ ((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n :=
            mul_le_mul hs1 hLLn (by norm_num) (by linarith)
          have hs3 : (6000:ℝ) * ((4:ℝ)/729) * ((4:ℝ)/9)
              ≤ (((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n) * (1 / Real.log x) :=
            mul_le_mul hs2 hinv (by norm_num) (by linarith [hs2])
          calc (piKFrom (n + 1) x p₀ : ℝ)
              ≤ x := hcount
            _ ≤ 9 := by linarith
            _ ≤ (6000:ℝ) * ((4:ℝ)/729) * ((4:ℝ)/9) := by norm_num
            _ ≤ (((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n) * (1 / Real.log x) := hs3
            _ = (C + 1) * 2000 * x * (Real.log (Real.log x)) ^ n / Real.log x := by ring
        · -- n >= 3: the count is literally zero since 2^(n+1) >= 16 > x
          have hzero : piKFrom (n + 1) x p₀ = 0 := by
            unfold piKFrom
            apply Finset.card_eq_zero.mpr
            apply Finset.filter_eq_empty_iff.mpr
            intro m hm
            simp only [Finset.mem_Icc] at hm
            intro hcontra
            obtain ⟨hmO, _⟩ := hcontra
            have hmge : 2 ^ (n + 1) ≤ m := by
              have hb := pow_bigOmega_le m (by omega)
              rw [hmO] at hb
              exact hb
            have h16 : 16 ≤ 2 ^ (n + 1) := by
              calc (16:ℕ) = 2 ^ 4 := by norm_num
                _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have hmle : (m:ℝ) ≤ x := by
              have h1 : (m:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hm.2
              have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
              linarith
            have h16r : (16:ℝ) ≤ (m:ℝ) := by
              exact_mod_cast le_trans h16 hmge
            linarith
          rw [hzero]
          simp only [Nat.cast_zero]
          have hLLpos : (0:ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
          apply div_nonneg _ hlx_pos.le
          apply mul_nonneg _ (pow_nonneg hLLpos.le n)
          apply mul_nonneg _ (by linarith : (0:ℝ) ≤ x)
          nlinarith [hC]

/-- Telescoping bound: partial sums of 1/(j*sqrt j) over [2,N] never exceed 2. -/
theorem telescope_sqrt (N : ℕ) :
    ∑ j ∈ Finset.Icc 2 N, (1:ℝ) / ((j:ℝ) * Real.sqrt j) ≤ 2 := by
  have hstep : ∀ M : ℕ,
      ∑ j ∈ Finset.Icc 2 M, (1:ℝ) / ((j:ℝ) * Real.sqrt j)
        ≤ 2 * (1 - 1 / Real.sqrt (M:ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rcases Nat.lt_or_ge M 1 with hM0 | hM1
      · have hM0' : M = 0 := by omega
        subst hM0'
        rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) by decide]
        simp
      · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
        have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
        have hsM : (0:ℝ) < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by linarith)
        have hsM1 : (0:ℝ) < Real.sqrt ((M:ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
        have hmulM : Real.sqrt (M:ℝ) * Real.sqrt (M:ℝ) = (M:ℝ) :=
          Real.mul_self_sqrt (by linarith)
        have hmulM1 : Real.sqrt ((M:ℝ) + 1) * Real.sqrt ((M:ℝ) + 1) = (M:ℝ) + 1 :=
          Real.mul_self_sqrt (by linarith)
        have hle : Real.sqrt (M:ℝ) ≤ Real.sqrt ((M:ℝ) + 1) :=
          Real.sqrt_le_sqrt (by linarith)
        have hkey : (Real.sqrt ((M:ℝ) + 1) - Real.sqrt (M:ℝ)) *
            (Real.sqrt ((M:ℝ) + 1) + Real.sqrt (M:ℝ)) = 1 := by
          nlinarith [hmulM, hmulM1]
        have hcast : (((M + 1 : ℕ)):ℝ) = (M:ℝ) + 1 := by push_cast; ring
        have htail : (1:ℝ) / (((M + 1 : ℕ):ℝ) * Real.sqrt ((M + 1 : ℕ):ℝ))
            ≤ 2 * (1 / Real.sqrt (M:ℝ) - 1 / Real.sqrt ((M:ℝ) + 1)) := by
          rw [hcast]
          have hdenom : (0:ℝ) < ((M:ℝ) + 1) * Real.sqrt ((M:ℝ) + 1) := by positivity
          rw [div_le_iff₀ hdenom]
          have hdiff : 1 / Real.sqrt (M:ℝ) - 1 / Real.sqrt ((M:ℝ) + 1)
              = (Real.sqrt ((M:ℝ) + 1) - Real.sqrt (M:ℝ)) /
                (Real.sqrt (M:ℝ) * Real.sqrt ((M:ℝ) + 1)) := by
            field_simp
            try ring
          rw [hdiff]
          have hab_pos : (0:ℝ) < Real.sqrt (M:ℝ) * Real.sqrt ((M:ℝ) + 1) := by
            positivity
          have hform : 2 * ((Real.sqrt ((M:ℝ) + 1) - Real.sqrt (M:ℝ)) /
                (Real.sqrt (M:ℝ) * Real.sqrt ((M:ℝ) + 1))) * (((M:ℝ) + 1) * Real.sqrt ((M:ℝ) + 1))
              = (2 * (Real.sqrt ((M:ℝ) + 1) - Real.sqrt (M:ℝ)) * (((M:ℝ) + 1) * Real.sqrt ((M:ℝ) + 1))) /
                (Real.sqrt (M:ℝ) * Real.sqrt ((M:ℝ) + 1)) := by
            ring
          rw [hform, le_div_iff₀ hab_pos]
          nlinarith [hkey, hle, hsM, hsM1, hmulM1, hmulM,
            mul_pos hsM hsM1,
            mul_nonneg (mul_nonneg hsM1.le hsM1.le) (sub_nonneg.mpr hle),
            mul_nonneg hsM1.le (sub_nonneg.mpr hle)]
        have hfinal : 2 * (1 - 1 / Real.sqrt (M:ℝ)) +
            2 * (1 / Real.sqrt (M:ℝ) - 1 / Real.sqrt ((M:ℝ) + 1))
            = 2 * (1 - 1 / Real.sqrt ((M:ℝ) + 1)) := by ring
        calc ∑ j ∈ Finset.Icc 2 M, (1:ℝ) / ((j:ℝ) * Real.sqrt j)
              + (1:ℝ) / (((M + 1 : ℕ):ℝ) * Real.sqrt ((M + 1 : ℕ):ℝ))
            ≤ 2 * (1 - 1 / Real.sqrt (M:ℝ)) +
              2 * (1 / Real.sqrt (M:ℝ) - 1 / Real.sqrt ((M:ℝ) + 1)) :=
              add_le_add ih htail
          _ = 2 * (1 - 1 / Real.sqrt ((M:ℝ) + 1)) := hfinal
          _ = 2 * (1 - 1 / Real.sqrt (((M + 1 : ℕ)):ℝ)) := by rw [hcast]
  calc ∑ j ∈ Finset.Icc 2 N, (1:ℝ) / ((j:ℝ) * Real.sqrt j)
      ≤ 2 * (1 - 1 / Real.sqrt (N:ℝ)) := hstep N
    _ ≤ 2 := by
        have h1 : (0:ℝ) ≤ 1 / Real.sqrt (N:ℝ) := by positivity
        linarith

/-- Power-of-log bound: (log y)^m ≤ (2m)^m * sqrt y for y >= 1, m >= 1. -/
theorem log_pow_le_sqrt (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 1 ≤ y) :
    (Real.log y) ^ m ≤ (2 * (m:ℝ)) ^ m * Real.sqrt y := by
  have hypos : (0:ℝ) < y := by linarith
  have hm_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_ne : (m:ℝ) ≠ 0 := hm_pos.ne'
  have h1 : Real.log (y ^ ((1:ℝ) / (2 * (m:ℝ)))) = (1 / (2 * (m:ℝ))) * Real.log y :=
    Real.log_rpow hypos _
  have h2 : Real.log (y ^ ((1:ℝ) / (2 * (m:ℝ)))) ≤ y ^ ((1:ℝ) / (2 * (m:ℝ))) :=
    Real.log_le_self (Real.rpow_nonneg hypos.le _)
  have h3 : (1 / (2 * (m:ℝ))) * Real.log y ≤ y ^ ((1:ℝ) / (2 * (m:ℝ))) := by
    rw [← h1]
    exact h2
  have hlog_le : Real.log y ≤ 2 * (m:ℝ) * y ^ ((1:ℝ) / (2 * (m:ℝ))) := by
    calc Real.log y = 2 * (m:ℝ) * ((1 / (2 * (m:ℝ))) * Real.log y) := by
          field_simp
      _ ≤ 2 * (m:ℝ) * y ^ ((1:ℝ) / (2 * (m:ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hlog_nn : (0:ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hp : (Real.log y) ^ m ≤ (2 * (m:ℝ) * y ^ ((1:ℝ) / (2 * (m:ℝ)))) ^ m := by
    apply pow_le_pow_left₀ hlog_nn hlog_le
  have hsplit : (2 * (m:ℝ) * y ^ ((1:ℝ) / (2 * (m:ℝ)))) ^ m
      = (2 * (m:ℝ)) ^ m * (y ^ ((1:ℝ) / (2 * (m:ℝ)))) ^ m := mul_pow _ _ _
  have hrpow : (y ^ ((1:ℝ) / (2 * (m:ℝ)))) ^ m = Real.sqrt y := by
    rw [← Real.rpow_natCast (y ^ ((1:ℝ) / (2 * (m:ℝ)))) m,
      ← Real.rpow_mul hypos.le]
    rw [show (1:ℝ) / (2 * (m:ℝ)) * (m:ℝ) = 1 / 2 by field_simp; try ring]
    rw [Real.sqrt_eq_rpow]
  calc (Real.log y) ^ m ≤ (2 * (m:ℝ) * y ^ ((1:ℝ) / (2 * (m:ℝ)))) ^ m := hp
    _ = (2 * (m:ℝ)) ^ m * (y ^ ((1:ℝ) / (2 * (m:ℝ)))) ^ m := hsplit
    _ = (2 * (m:ℝ)) ^ m * Real.sqrt y := by rw [hrpow]

/-- The summand 1/(t log t) is antitone past 2. -/
theorem inv_mul_log_le (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    1 / (b * Real.log b) ≤ 1 / (a * Real.log a) := by
  have hla : (0:ℝ) < Real.log a := Real.log_pos (by linarith)
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpa : (0:ℝ) < a * Real.log a := mul_pos (by linarith) hla
  apply one_div_le_one_div_of_le hpa
  apply mul_le_mul hab hlb hla.le (by linarith)

/-- Nonzero terms in dyadic block j inject into the piK count at 2^(j+1). -/
theorem block_count_le_piK (kk j M : ℕ) :
    (((Finset.Ioc 1 M).filter (fun n => Nat.log 2 n = j)).filter
        (fun n => 2 ≤ n ∧ bigOmega n = kk)).card
      ≤ piK kk (((2:ℕ) ^ (j + 1) : ℕ) : ℝ) := by
  classical
  unfold piK
  rw [Nat.floor_natCast]
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnf, hn2, hnO⟩ := Finset.mem_filter.mp hn
  have hb := dyadic_fiber_mem_bounds 1 M j n hnf
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn2, by omega⟩, hnO⟩

/-- Per-block arithmetic: the piK bound value at 2^(j+1) times the max term size
in block j is at most K / (j * sqrt j), with K explicit. -/
theorem block_arith (C : ℝ) (hC : 0 < C) (m j : ℕ) (hj : 1 ≤ j) :
    C * (2:ℝ) ^ (j + 1) * (Real.log (Real.log ((2:ℝ) ^ (j + 1)))) ^ m /
        Real.log ((2:ℝ) ^ (j + 1)) * (1 / ((2:ℝ) ^ j * Real.log ((2:ℝ) ^ j)))
      ≤ 4 * C * (2 * (m:ℝ)) ^ m / (Real.log 2) ^ 2 * (1 / ((j:ℝ) * Real.sqrt j)) := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hl2h : (1:ℝ) / 2 ≤ Real.log 2 := by
    have hsq : Real.exp ((1:ℝ) / 2) * Real.exp ((1:ℝ) / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have he := Real.exp_one_lt_d9
    have hp := Real.exp_pos ((1:ℝ) / 2)
    have h2 : Real.exp ((1:ℝ) / 2) ≤ 2 := by nlinarith
    have h2' : Real.log (Real.exp ((1:ℝ) / 2)) ≤ Real.log 2 :=
      Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h2'
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hjR : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj1pos : (0:ℝ) < (j:ℝ) + 1 := by linarith
  have hsj : (0:ℝ) < Real.sqrt j := Real.sqrt_pos.mpr hjpos
  have hjj : Real.sqrt j * Real.sqrt j = (j:ℝ) := Real.mul_self_sqrt hjpos.le
  have hA : (0:ℝ) < (2:ℝ) ^ j := by positivity
  have hlogj : Real.log ((2:ℝ) ^ j) = (j:ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogj1 : Real.log ((2:ℝ) ^ (j + 1)) = ((j:ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogj, hlogj1]
  have hll_ub : Real.log (((j:ℝ) + 1) * Real.log 2) ≤ Real.log ((j:ℝ) + 1) := by
    apply Real.log_le_log (mul_pos hj1pos hl2)
    nlinarith [hl2', hj1pos]
  have hll_nn : (0:ℝ) ≤ Real.log (((j:ℝ) + 1) * Real.log 2) := by
    apply Real.log_nonneg
    nlinarith [hl2h, hjR, mul_nonneg (by linarith : (0:ℝ) ≤ (j:ℝ) - 1) hl2.le]
  have hpow1 : (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m ≤ (Real.log ((j:ℝ) + 1)) ^ m := by
    apply pow_le_pow_left₀ hll_nn hll_ub
  have hLP : (Real.log ((j:ℝ) + 1)) ^ m ≤ (2 * (m:ℝ)) ^ m * Real.sqrt ((j:ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · subst hm0
      simp only [pow_zero, one_mul]
      have h1 : Real.sqrt 1 ≤ Real.sqrt ((j:ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_one] at h1
      linarith
    · exact log_pow_le_sqrt m hm1 ((j:ℝ) + 1) (by linarith)
  have hsq1 : Real.sqrt ((j:ℝ) + 1) ≤ 2 * Real.sqrt j := by
    have h4 : Real.sqrt ((j:ℝ) + 1) ≤ Real.sqrt (4 * (j:ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h5 : Real.sqrt (4 * (j:ℝ)) = 2 * Real.sqrt j := by
      rw [show (4:ℝ) * (j:ℝ) = (2:ℝ) ^ 2 * (j:ℝ) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h5] at h4
    exact h4
  have hX : (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m
      ≤ (2 * (m:ℝ)) ^ m * (2 * Real.sqrt j) := by
    have h3 : (2 * (m:ℝ)) ^ m * Real.sqrt ((j:ℝ) + 1)
        ≤ (2 * (m:ℝ)) ^ m * (2 * Real.sqrt j) :=
      mul_le_mul_of_nonneg_left hsq1 (pow_nonneg (by positivity) m)
    linarith [hpow1, hLP, h3]
  have hE1 : C * (2:ℝ) ^ (j + 1) * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m /
        (((j:ℝ) + 1) * Real.log 2) * (1 / ((2:ℝ) ^ j * ((j:ℝ) * Real.log 2)))
      = 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m /
        (((j:ℝ) + 1) * (j:ℝ) * (Real.log 2) ^ 2) := by
    rw [pow_succ]
    field_simp
    try ring
  have hEL : 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m /
        (((j:ℝ) + 1) * (j:ℝ) * (Real.log 2) ^ 2)
      = 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j:ℝ) + 1) * (j:ℝ))) * (1 / (Real.log 2) ^ 2) := by
    field_simp [hl2.ne', hjpos.ne', hj1pos.ne']
    try ring
  have hinv : 1 / (((j:ℝ) + 1) * (j:ℝ)) ≤ 1 / ((j:ℝ) * (j:ℝ)) := by
    apply one_div_le_one_div_of_le (mul_pos hjpos hjpos)
    nlinarith [hjpos]
  have hK0 : (0:ℝ) ≤ 2 * C * ((2 * (m:ℝ)) ^ m * (2 * Real.sqrt j)) := by
    apply mul_nonneg (by linarith)
    apply mul_nonneg (pow_nonneg (by positivity) m)
    positivity
  have hstep1 : 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m
      ≤ 2 * C * ((2 * (m:ℝ)) ^ m * (2 * Real.sqrt j)) :=
    mul_le_mul_of_nonneg_left hX (by linarith)
  have hstep2 : 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j:ℝ) + 1) * (j:ℝ)))
      ≤ 2 * C * ((2 * (m:ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j:ℝ) * (j:ℝ))) :=
    mul_le_mul hstep1 hinv (le_of_lt (one_div_pos.mpr (mul_pos hj1pos hjpos))) hK0
  have hstep3 : 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j:ℝ) + 1) * (j:ℝ))) * (1 / (Real.log 2) ^ 2)
      ≤ 2 * C * ((2 * (m:ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j:ℝ) * (j:ℝ))) *
        (1 / (Real.log 2) ^ 2) :=
    mul_le_mul_of_nonneg_right hstep2 (le_of_lt (one_div_pos.mpr (pow_pos hl2 2)))
  have hER : 2 * C * ((2 * (m:ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j:ℝ) * (j:ℝ))) *
        (1 / (Real.log 2) ^ 2)
      = 4 * C * (2 * (m:ℝ)) ^ m / (Real.log 2) ^ 2 * (Real.sqrt j / ((j:ℝ) * (j:ℝ))) := by
    ring
  have hfrac : Real.sqrt j / ((j:ℝ) * (j:ℝ)) = 1 / ((j:ℝ) * Real.sqrt j) := by
    rw [div_eq_div_iff (mul_pos hjpos hjpos).ne' (mul_pos hjpos hsj).ne']
    linear_combination (j:ℝ) * hjj
  calc C * (2:ℝ) ^ (j + 1) * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m /
        (((j:ℝ) + 1) * Real.log 2) * (1 / ((2:ℝ) ^ j * ((j:ℝ) * Real.log 2)))
      = 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m /
        (((j:ℝ) + 1) * (j:ℝ) * (Real.log 2) ^ 2) := hE1
    _ = 2 * C * (Real.log (((j:ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j:ℝ) + 1) * (j:ℝ))) * (1 / (Real.log 2) ^ 2) := hEL
    _ ≤ 2 * C * ((2 * (m:ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j:ℝ) * (j:ℝ))) *
        (1 / (Real.log 2) ^ 2) := hstep3
    _ = 4 * C * (2 * (m:ℝ)) ^ m / (Real.log 2) ^ 2 *
        (Real.sqrt j / ((j:ℝ) * (j:ℝ))) := hER
    _ = 4 * C * (2 * (m:ℝ)) ^ m / (Real.log 2) ^ 2 * (1 / ((j:ℝ) * Real.sqrt j)) := by
        rw [hfrac]

/-- Manuscript Definition 2.3: S(m) = sum_{j+l=m} int_1^2 (-log(s-1))^l/l! * 2^(-js) ds.
Indexed by j in range (m+1), with l = m - j. -/
noncomputable def Sm (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ∫ s in Set.Ioc (1:ℝ) 2,
      (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (2:ℝ) ^ (-(j:ℝ) * s)
      ∂MeasureTheory.volume

/-- Manuscript Definition 2.3: A_m = 2^m S(m). -/
noncomputable def Am (m : ℕ) : ℝ := 2 ^ m * Sm m

/-- Manuscript Definition 2.3: delta_m = A_m - 2^(m+1) + (log 2 / 4) m^2.
GLW Lemma 3.3 is the estimate delta_m = O(m log(m+1)); manuscript Theorem 4.1
is the explicit two-sided bound. -/
noncomputable def deltaM (m : ℕ) : ℝ :=
  Am m - 2 ^ (m + 1) + (Real.log 2 / 4) * (m : ℝ) ^ 2

/-- Anchor: S(0) = 1 (single term j = 0, integrand identically 1). -/
theorem Sm_zero : Sm 0 = 1 := by
  unfold Sm
  rw [Finset.sum_range_one]
  have hintegrand : ∀ s : ℝ,
      (-Real.log (s - 1)) ^ (0 - 0) / (Nat.factorial (0 - 0)) * (2:ℝ) ^ (-((0:ℕ):ℝ) * s)
        = 1 := by
    intro s
    norm_num
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s _ => hintegrand s)]
  rw [MeasureTheory.setIntegral_const]
  have hvol : MeasureTheory.volume.real (Set.Ioc (1:ℝ) 2) = 1 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc]
    norm_num
  rw [hvol]
  norm_num

/-- Anchor: A_0 = 1. -/
theorem Am_zero : Am 0 = 1 := by
  unfold Am
  rw [Sm_zero]
  norm_num

/-- Manuscript Proposition 3.3 spot value, proven: delta_0 = -1 exactly. -/
theorem deltaM_zero : deltaM 0 = -1 := by
  unfold deltaM
  rw [Am_zero]
  norm_num

/-- The Gamma evaluation: int_{u>0} e^(-u) u^i du = i!. Foundation for the
substitution identity (manuscript eq (5)) and Theorem 4.1. -/
theorem integral_exp_neg_mul_pow (i : ℕ) :
    ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ i = (Nat.factorial i : ℝ) := by
  calc ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ i
      = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (((i:ℝ) + 1) - 1) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [show ((i:ℝ) + 1) - 1 = (i:ℝ) by ring, Real.rpow_natCast]
    _ = Real.Gamma ((i:ℝ) + 1) := (Real.Gamma_eq_integral (by positivity)).symm
    _ = (Nat.factorial i : ℝ) := Real.Gamma_nat_eq_factorial i

/-- Manuscript eq (5): J(i) for block m, as an integral over u > 0. -/
noncomputable def Jint (m i : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0:ℝ),
    u ^ i * Real.exp (-u) * (2:ℝ) ^ (-((m - i : ℕ):ℝ) * Real.exp (-u))

/-- Anchor: J(0) at m = 0 is 1 (the integrand collapses to e^(-u)). -/
theorem Jint_zero : Jint 0 0 = 1 := by
  unfold Jint
  have hcong : ∀ u : ℝ,
      u ^ 0 * Real.exp (-u) * (2:ℝ) ^ (-(((0:ℕ) - 0 : ℕ):ℝ) * Real.exp (-u))
        = Real.exp (-u) * u ^ 0 := by
    intro u
    norm_num
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => hcong u)]
  rw [integral_exp_neg_mul_pow 0]
  norm_num

/-- The substitution map s = 1 + e^(-u) sends (0, infty) onto (1, 2). -/
theorem subst_image :
    (fun u : ℝ => 1 + Real.exp (-u)) '' Set.Ioi 0 = Set.Ioo 1 2 := by
  ext s
  simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨u, hu, rfl⟩
    constructor
    · have h := Real.exp_pos (-u)
      linarith
    · have h1 : Real.exp (-u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      rw [Real.exp_zero] at h1
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨-Real.log (s - 1), ?_, ?_⟩
    · have hlog : Real.log (s - 1) < 0 :=
        Real.log_neg (by linarith) (by linarith)
      linarith
    · show 1 + Real.exp (-(-Real.log (s - 1))) = s
      rw [neg_neg, Real.exp_log (by linarith)]
      ring

/-- The substitution map is injective on (0, infty). -/
theorem subst_injOn :
    Set.InjOn (fun u : ℝ => 1 + Real.exp (-u)) (Set.Ioi 0) := by
  intro u _ v _ huv
  simp only [add_right_inj] at huv
  have h3 := Real.exp_injective huv
  linarith

/-- Change of variables s = 1 + e^(-u): integrals over (1, 2] become
e^(-u)-weighted integrals over (0, infty). Workhorse for manuscript eq (5). -/
theorem integral_Ioc_subst (g : ℝ → ℝ) :
    ∫ s in Set.Ioc (1:ℝ) 2, g s
      = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * g (1 + Real.exp (-u)) := by
  have hderiv : ∀ u ∈ Set.Ioi (0:ℝ),
      HasDerivWithinAt (fun u : ℝ => 1 + Real.exp (-u))
        (Real.exp (-u) * (-1)) (Set.Ioi 0) u := by
    intro u _
    exact (((hasDerivAt_neg u).exp).const_add 1).hasDerivWithinAt
  have himg := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv subst_injOn g
  rw [subst_image] at himg
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, himg]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [smul_eq_mul, mul_neg_one, abs_neg, abs_of_pos (Real.exp_pos _)]

/-- Manuscript eq (5): A_m = sum_{i <= m} 2^i / i! * J(i), by the substitution
s = 1 + e^(-u) applied termwise and reflecting the sum index. -/
theorem Am_eq_sum_Jint (m : ℕ) :
    Am m = ∑ i ∈ Finset.range (m + 1),
      (2:ℝ) ^ i / (Nat.factorial i) * Jint m i := by
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (2:ℝ) ^ m * ∫ s in Set.Ioc (1:ℝ) 2,
          (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (2:ℝ) ^ (-(j:ℝ) * s)
        = (2:ℝ) ^ (m - j) / (Nat.factorial (m - j)) * Jint m (m - j) := by
    intro j hjm
    have hj : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjm)
    have h2mj : (2:ℝ) ^ (m:ℕ) * (2:ℝ) ^ (-(j:ℝ)) = (2:ℝ) ^ ((m - j : ℕ)) := by
      rw [← Real.rpow_natCast (2:ℝ) m, ← Real.rpow_natCast (2:ℝ) (m - j),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2), Nat.cast_sub hj]
      try congr 1
      try ring
    rw [integral_Ioc_subst]
    unfold Jint
    rw [Nat.sub_sub_self hj]
    rw [← MeasureTheory.integral_const_mul]
    conv_rhs => rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
    rw [show -(j:ℝ) * (1 + Real.exp (-u)) = -(j:ℝ) + -(j:ℝ) * Real.exp (-u) by ring]
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    field_simp
    rw [← h2mj]
    ring
  calc Am m = ∑ j ∈ Finset.range (m + 1),
        (2:ℝ) ^ m * ∫ s in Set.Ioc (1:ℝ) 2,
          (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (2:ℝ) ^ (-(j:ℝ) * s) := by
        unfold Am Sm
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (m + 1),
        (2:ℝ) ^ (m - j) / (Nat.factorial (m - j)) * Jint m (m - j) :=
        Finset.sum_congr rfl hterm
    _ = ∑ i ∈ Finset.range (m + 1),
        (2:ℝ) ^ i / (Nat.factorial i) * Jint m i := by
        exact Finset.sum_range_reflect (fun i => (2:ℝ) ^ i / (Nat.factorial i) * Jint m i) (m + 1)

/-- Manuscript Thm 4.1: B_j(u) = 2^(-j e^(-u)) - 1 + j log 2 e^(-u), the
convexity gap driving identity (11). -/
noncomputable def Bfun (j : ℕ) (u : ℝ) : ℝ :=
  (2:ℝ) ^ (-(j:ℝ) * Real.exp (-u)) - 1 + (j:ℝ) * Real.log 2 * Real.exp (-u)

/-- B_j(u) >= 0: from e^x >= 1 + x at x = -(j log 2) e^(-u). -/
theorem Bfun_nonneg (j : ℕ) (u : ℝ) : 0 ≤ Bfun j u := by
  unfold Bfun
  have hrw : (2:ℝ) ^ (-(j:ℝ) * Real.exp (-u))
      = Real.exp (-(j:ℝ) * Real.exp (-u) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    ring_nf
  rw [hrw]
  have h := Real.add_one_le_exp (-(j:ℝ) * Real.exp (-u) * Real.log 2)
  nlinarith [h]

/-- Manuscript (11): beta-circle, the nonnegative integral coefficient. -/
noncomputable def betaCirc (i j : ℕ) : ℝ :=
  (1 / (Nat.factorial i : ℝ)) *
    ∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-u) * Bfun j u

/-- The scaled Gamma evaluation: int_{u>0} u^i e^(-2u) du = i! / 2^(i+1),
via the linear substitution u = v/2. -/
theorem integral_pow_exp_neg_two_mul (i : ℕ) :
    ∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-(2 * u))
      = (Nat.factorial i : ℝ) / 2 ^ (i + 1) := by
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
    (fun v => v ^ i * Real.exp (-v)) (0:ℝ) (by norm_num : (0:ℝ) < 2)
  simp only [mul_zero] at hcomp
  have hcong : ∀ u ∈ Set.Ioi (0:ℝ),
      u ^ i * Real.exp (-(2 * u)) = ((2 * u) ^ i * Real.exp (-(2 * u))) / 2 ^ i := by
    intro u _
    rw [mul_pow]
    field_simp
    try ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcong]
  rw [MeasureTheory.integral_div]
  rw [show (∫ u in Set.Ioi (0:ℝ), (2 * u) ^ i * Real.exp (-(2 * u)))
      = ∫ u in Set.Ioi (0:ℝ), (fun v => v ^ i * Real.exp (-v)) (2 * u) from rfl]
  rw [hcomp]
  have hbase : ∫ v in Set.Ioi (0:ℝ), v ^ i * Real.exp (-v)
      = (Nat.factorial i : ℝ) := by
    rw [← integral_exp_neg_mul_pow i]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    simp only
    ring
  rw [smul_eq_mul, hbase]
  rw [show ((2:ℝ))⁻¹ = 1 / 2 by norm_num]
  field_simp
  try ring

/-- Integrability of the Gamma integrand u^i e^(-u) on (0, infty). -/
theorem integrable_pow_exp (i : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ i * Real.exp (-u)) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (i:ℝ) + 1) (by positivity)
  apply h.congr_fun ?_ measurableSet_Ioi
  intro u hu
  simp only
  rw [show ((i:ℝ) + 1) - 1 = (i:ℝ) by ring, Real.rpow_natCast]
  ring

/-- Integrability of u^i e^(-2u) on (0, infty), by domination. -/
theorem integrable_pow_exp_two (i : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ i * Real.exp (-(2 * u))) (Set.Ioi 0) := by
  apply MeasureTheory.Integrable.mono (integrable_pow_exp i)
    (by fun_prop : Continuous fun u : ℝ => u ^ i * Real.exp (-(2 * u))).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0:ℝ) < u := Set.mem_Ioi.mp hu
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le),
    abs_of_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu0.le i)
  apply Real.exp_le_exp.mpr
  linarith

/-- Integrability of the J-integrand: the damping factor is at most 1. -/
theorem integrable_Jint_integrand (c : ℝ) (hc : 0 ≤ c) (i : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ i * Real.exp (-u) * (2:ℝ) ^ (-c * Real.exp (-u)))
      (Set.Ioi 0) := by
  have hfeq : (fun u : ℝ => u ^ i * Real.exp (-u) * (2:ℝ) ^ (-c * Real.exp (-u)))
      = fun u : ℝ => u ^ i * Real.exp (-u) * Real.exp (-c * Real.exp (-u) * Real.log 2) := by
    funext u
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    ring_nf
  rw [hfeq]
  apply MeasureTheory.Integrable.mono (integrable_pow_exp i)
    (by fun_prop :
      Continuous fun u : ℝ => u ^ i * Real.exp (-u) * Real.exp (-c * Real.exp (-u) * Real.log 2)).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0:ℝ) < u := Set.mem_Ioi.mp hu
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -c * Real.exp (-u) * Real.log 2 ≤ 0 := by
    have h1 : (0:ℝ) ≤ c * Real.exp (-u) * Real.log 2 :=
      mul_nonneg (mul_nonneg hc (Real.exp_pos _).le) hl2.le
    linarith
  have hdamp : Real.exp (-c * Real.exp (-u) * Real.log 2) ≤ 1 := by
    calc Real.exp (-c * Real.exp (-u) * Real.log 2) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr harg
      _ = 1 := Real.exp_zero
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)
      (Real.exp_pos _).le),
    abs_of_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)]
  calc u ^ i * Real.exp (-u) * Real.exp (-c * Real.exp (-u) * Real.log 2)
      ≤ u ^ i * Real.exp (-u) * 1 :=
        mul_le_mul_of_nonneg_left hdamp
          (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)
    _ = u ^ i * Real.exp (-u) := mul_one _

/-- The J-split (manuscript Thm 4.1 engine): J(i) decomposes exactly into the
Bfun piece, the Gamma piece, and the log2-weighted scaled piece. -/
theorem Jint_split (m i : ℕ) :
    Jint m i = (Nat.factorial i : ℝ) * betaCirc i (m - i)
      + (Nat.factorial i : ℝ)
      - ((m - i : ℕ) : ℝ) * Real.log 2 * ((Nat.factorial i : ℝ) / 2 ^ (i + 1)) := by
  have hfacne : ((Nat.factorial i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hpt : ∀ u : ℝ,
      u ^ i * Real.exp (-u) * (2:ℝ) ^ (-(((m - i : ℕ)):ℝ) * Real.exp (-u))
        = u ^ i * Real.exp (-u) * Bfun (m - i) u
          + u ^ i * Real.exp (-u)
          - ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))) := by
    intro u
    have hexp : Real.exp (-u) * Real.exp (-u) = Real.exp (-(2 * u)) := by
      rw [← Real.exp_add]
      ring_nf
    unfold Bfun
    rw [show Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) from hexp.symm]
    ring
  have hI1 := integrable_pow_exp i
  have hI2 := integrable_pow_exp_two i
  have hI3 := integrable_Jint_integrand (((m - i : ℕ)):ℝ) (by positivity) i
  have hIB : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ i * Real.exp (-u) * Bfun (m - i) u) (Set.Ioi 0) := by
    have hfeq : (fun u : ℝ => u ^ i * Real.exp (-u) * Bfun (m - i) u)
        = fun u : ℝ =>
          (u ^ i * Real.exp (-u) * (2:ℝ) ^ (-(((m - i : ℕ)):ℝ) * Real.exp (-u))
            - u ^ i * Real.exp (-u))
          + ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))) := by
      funext u
      have h := hpt u
      linarith [h]
    rw [hfeq]
    exact (hI3.sub hI1).add (hI2.const_mul _)
  have hbase : ∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-u)
      = (Nat.factorial i : ℝ) := by
    rw [← integral_exp_neg_mul_pow i]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only
    ring
  have hbeta : ∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-u) * Bfun (m - i) u
      = (Nat.factorial i : ℝ) * betaCirc i (m - i) := by
    unfold betaCirc
    field_simp
  unfold Jint
  calc ∫ u in Set.Ioi (0:ℝ),
        u ^ i * Real.exp (-u) * (2:ℝ) ^ (-(((m - i : ℕ)):ℝ) * Real.exp (-u))
      = ∫ u in Set.Ioi (0:ℝ),
        (u ^ i * Real.exp (-u) * Bfun (m - i) u + u ^ i * Real.exp (-u)
          - ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u)))) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [hpt u]
    _ = (∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-u) * Bfun (m - i) u)
        + (∫ u in Set.Ioi (0:ℝ), u ^ i * Real.exp (-u))
        - ∫ u in Set.Ioi (0:ℝ),
            ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))) := by
        have hIsum : MeasureTheory.IntegrableOn
            (fun u : ℝ => u ^ i * Real.exp (-u) * Bfun (m - i) u + u ^ i * Real.exp (-u))
            (Set.Ioi 0) := hIB.add hI1
        have hIc : MeasureTheory.IntegrableOn
            (fun u : ℝ => ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))))
            (Set.Ioi 0) := hI2.const_mul _
        rw [MeasureTheory.integral_sub hIsum hIc, MeasureTheory.integral_add hIB hI1]
    _ = (Nat.factorial i : ℝ) * betaCirc i (m - i) + (Nat.factorial i : ℝ)
        - ((m - i : ℕ) : ℝ) * Real.log 2 * ((Nat.factorial i : ℝ) / 2 ^ (i + 1)) := by
        rw [hbeta, hbase, MeasureTheory.integral_const_mul, integral_pow_exp_neg_two_mul]

/-- Closed form: sum_{i <= m} (m - i) = m(m+1)/2, over the reals. -/
theorem sum_range_sub_cast (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), ((m - i : ℕ) : ℝ)
      = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ']
    have hcong : ∀ i ∈ Finset.range (M + 1),
        (((M + 1 - (i + 1) : ℕ)) : ℝ) = ((M - i : ℕ) : ℝ) := by
      intro i _
      congr 1
      omega
    rw [Finset.sum_congr rfl hcong, ih]
    push_cast
    ring

/-- Identity (11): delta_m = -1 - (log 2 / 4) m + sum_{i <= m} 2^i beta-circle(i, m-i). -/
theorem deltaM_identity (m : ℕ) :
    deltaM m = -1 - (Real.log 2 / 4) * (m : ℝ)
      + ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * betaCirc i (m - i) := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (2:ℝ) ^ i / (Nat.factorial i) * Jint m i
        = (2:ℝ) ^ i * betaCirc i (m - i) + (2:ℝ) ^ i
          - ((m - i : ℕ) : ℝ) * Real.log 2 / 2 := by
    intro i _
    rw [Jint_split m i]
    have hfacne : ((Nat.factorial i : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have h2 : (2:ℝ) ^ (i + 1) = 2 ^ i * 2 := by ring
    field_simp [h2]
    ring
  have hsum : ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i / (Nat.factorial i) * Jint m i
      = (∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * betaCirc i (m - i))
        + (∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i)
        - (∑ i ∈ Finset.range (m + 1), ((m - i : ℕ) : ℝ) * Real.log 2 / 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have hgeom : ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i = 2 ^ (m + 1) - 1 := by
    have := geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) (m + 1)
    rw [this]
    ring
  have hlin : ∑ i ∈ Finset.range (m + 1), ((m - i : ℕ) : ℝ) * Real.log 2 / 2
      = (Real.log 2 / 2) * ((m : ℝ) * ((m : ℝ) + 1) / 2) := by
    rw [← sum_range_sub_cast m, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold deltaM
  rw [Am_eq_sum_Jint m, hsum, hgeom, hlin]
  ring

/-- betaCirc is nonnegative: the integrand is a product of nonnegatives. -/
theorem betaCirc_nonneg (i j : ℕ) : 0 ≤ betaCirc i j := by
  unfold betaCirc
  apply mul_nonneg
  · positivity
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro u hu
    have hu0 : (0:ℝ) < u := Set.mem_Ioi.mp hu
    apply mul_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)
    exact Bfun_nonneg j u

/-- MANUSCRIPT THEOREM 4.1, LOWER BOUND: delta_m >= -1 - (log 2 / 4) m,
for every m. Immediate from identity (11) and nonnegativity of beta-circle. -/
theorem deltaM_lower_bound (m : ℕ) :
    -1 - (Real.log 2 / 4) * (m : ℝ) ≤ deltaM m := by
  rw [deltaM_identity m]
  have hsum : (0:ℝ) ≤
      ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * betaCirc i (m - i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by positivity) (betaCirc_nonneg i (m - i))
  linarith

/-- Manuscript Thm 4.1: B_j is increasing in j (the 2^(-j e^-u) factor shrinks
faster than the linear term grows). Stated as the comparison needed there. -/
theorem Bfun_mono (j m : ℕ) (hjm : j ≤ m) (u : ℝ) :
    Bfun j u ≤ Bfun m u := by
  unfold Bfun
  have hE : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
  have hjR : ((j:ℕ):ℝ) ≤ ((m:ℕ):ℝ) := by exact_mod_cast hjm
  have hgap : (2:ℝ) ^ (-((m:ℕ):ℝ) * Real.exp (-u))
      - (2:ℝ) ^ (-((j:ℕ):ℝ) * Real.exp (-u))
      + (((m:ℕ):ℝ) - ((j:ℕ):ℝ)) * Real.log 2 * Real.exp (-u) ≥ 0 := by
    set c := ((m:ℕ):ℝ) - ((j:ℕ):ℝ) with hc
    have hc0 : (0:ℝ) ≤ c := by rw [hc]; linarith
    have hrw1 : (2:ℝ) ^ (-((m:ℕ):ℝ) * Real.exp (-u))
        = (2:ℝ) ^ (-((j:ℕ):ℝ) * Real.exp (-u)) *
          (2:ℝ) ^ (-c * Real.exp (-u)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      rw [hc]
      ring
    have hbase : (0:ℝ) < (2:ℝ) ^ (-((j:ℕ):ℝ) * Real.exp (-u)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hbase_le : (2:ℝ) ^ (-((j:ℕ):ℝ) * Real.exp (-u)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (0:ℝ) ≤ ((j:ℕ):ℝ) * Real.exp (-u) :=
        mul_nonneg (Nat.cast_nonneg j) hE.le
      linarith
    have hB := Bfun_nonneg 0 u
    have hkey : (1:ℝ) - (2:ℝ) ^ (-c * Real.exp (-u))
        ≤ c * Real.log 2 * Real.exp (-u) := by
      have hexp : (2:ℝ) ^ (-c * Real.exp (-u))
          = Real.exp (-c * Real.exp (-u) * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
        ring_nf
      rw [hexp]
      have h := Real.add_one_le_exp (-c * Real.exp (-u) * Real.log 2)
      linarith
    rw [hrw1]
    have hA : (0:ℝ) < (2:ℝ) ^ (-c * Real.exp (-u)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hstep : (2:ℝ) ^ (-(↑j) * Real.exp (-u)) *
        (1 - (2:ℝ) ^ (-c * Real.exp (-u)))
        ≤ 1 - (2:ℝ) ^ (-c * Real.exp (-u)) := by
      have hnn : (0:ℝ) ≤ 1 - (2:ℝ) ^ (-c * Real.exp (-u)) := by
        have : (2:ℝ) ^ (-c * Real.exp (-u)) ≤ 1 := by
          apply rpow_le_one_of_one_le_of_nonpos (by norm_num)
          nlinarith [hc0, hE]
        linarith
      nlinarith [hbase_le, hnn]
    nlinarith [hstep, hkey]
  linarith [hgap]

/-- Partial sums of the exponential series are bounded by the exponential. -/
theorem sum_pow_div_factorial_le_exp (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), x ^ i / (Nat.factorial i) ≤ Real.exp x := by
  have hsum : Summable (fun i : ℕ => x ^ i / (Nat.factorial i : ℝ)) :=
    Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' i : ℕ, x ^ i / (Nat.factorial i : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp]
  apply hsum.sum_le_tsum
  intro i _
  positivity


/-- The betaCirc integrand is integrable on (0, infty). -/
theorem integrable_betaCirc_integrand (i j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ i * Real.exp (-u) * Bfun j u) (Set.Ioi 0) := by
  have hI1 := integrable_pow_exp i
  have hI2 := integrable_pow_exp_two i
  have hI3 := integrable_Jint_integrand ((j:ℕ):ℝ) (by positivity) i
  have hfeq : (fun u : ℝ => u ^ i * Real.exp (-u) * Bfun j u)
      = fun u : ℝ =>
        (u ^ i * Real.exp (-u) * (2:ℝ) ^ (-((j:ℕ):ℝ) * Real.exp (-u))
          - u ^ i * Real.exp (-u))
        + ((j:ℕ):ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))) := by
    funext u
    unfold Bfun
    have hexp : Real.exp (-u) * Real.exp (-u) = Real.exp (-(2 * u)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [show Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) from hexp.symm]
    ring
  rw [hfeq]
  exact (hI3.sub hI1).add (hI2.const_mul _)

/-- Per-term monotonicity: betaCirc i j is monotone in j (from Bfun_mono). -/
theorem betaCirc_mono (i j m : ℕ) (hjm : j ≤ m) :
    betaCirc i j ≤ betaCirc i m := by
  unfold betaCirc
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply MeasureTheory.setIntegral_mono_on
    (integrable_betaCirc_integrand i j) (integrable_betaCirc_integrand i m)
    measurableSet_Ioi
  intro u hu
  have hu0 : (0:ℝ) < u := hu
  apply mul_le_mul_of_nonneg_left (Bfun_mono j m hjm u)
  positivity

/-- Replace the varying index: sum 2^i betaCirc i (m-i) <= sum 2^i betaCirc i m. -/
theorem sum_betaCirc_le_uniform (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * betaCirc i (m - i)
      ≤ ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * betaCirc i m := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact betaCirc_mono i (m - i) m (Nat.sub_le m i)

/-- DEEP FACT (Landau, elementary form; now formalized via piKFrom_bound): the count of
    k-almost-primes up to x is O(x (log log x)^(k-1) / log x). Stated with
    an explicit witness constant C_k rather than raw big-O, since the O
    needs to be usable inside a partial-summation argument. This is the one
    piece of real analytic number theory in the whole formalization; every
    other lemma in this file is either algebra or follows from this one. -/
lemma piK_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      (piK k x : ℝ) ≤ C * x * (Real.log (Real.log x)) ^ (k - 1) / Real.log x := by
  obtain ⟨C, hC, hbound⟩ := piKFrom_bound k hk
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [piK_eq_piKFrom_two]
  exact hbound 2 x hx

/-- Given the counting bound, convergence follows by partial summation
    (Abel summation against π_k, using log n → ∞ to kill the count's
    polynomial-in-log-log growth). Standard once piK_bound is in hand. -/
lemma fk_summable (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) * Real.log n)) := by
  obtain ⟨C, hC, hbound⟩ := piK_bound k hk
  classical
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hind : Summable (Set.indicator {n : ℕ | 2 ≤ n ∧ bigOmega n = k}
      (fun n : ℕ => 1 / ((n:ℝ) * Real.log n))) := by
    set I := Set.indicator {n : ℕ | 2 ≤ n ∧ bigOmega n = k}
      (fun n : ℕ => 1 / ((n:ℝ) * Real.log n)) with hI
    have hInn : ∀ n : ℕ, 0 ≤ I n := by
      intro n
      rw [hI]
      apply Set.indicator_nonneg
      intro a ha
      obtain ⟨ha2, _⟩ := ha
      have haR : (2:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha2
      have hla : (0:ℝ) < Real.log a := Real.log_pos (by linarith)
      exact le_of_lt (one_div_pos.mpr (mul_pos (by linarith) hla))
    have hIvan : ∀ n : ℕ, ¬(2 ≤ n ∧ bigOmega n = k) → I n = 0 := by
      intro n hn
      rw [hI, Set.indicator_apply,
        if_neg (show n ∉ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} from fun hmem => hn hmem)]
    have hImem : ∀ n : ℕ, 2 ≤ n → bigOmega n = k →
        I n = 1 / ((n:ℝ) * Real.log n) := by
      intro n h2 hO
      rw [hI, Set.indicator_apply,
        if_pos (show n ∈ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} from ⟨h2, hO⟩)]
    have hblock : ∀ N j : ℕ, 1 ≤ j →
        ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n
          ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
            (1 / ((j:ℝ) * Real.sqrt j)) := by
      intro N j hj
      have hdz : ∑ n ∈ ((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
            (fun n => 2 ≤ n ∧ bigOmega n = k), I n
          = ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro n hn hnP
        apply hIvan
        intro hmem
        exact hnP (Finset.mem_filter.mpr ⟨hn, hmem⟩)
      rw [← hdz]
      have hterm : ∀ n ∈ ((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
          (fun n => 2 ≤ n ∧ bigOmega n = k),
          I n ≤ 1 / ((2:ℝ) ^ j * Real.log ((2:ℝ) ^ j)) := by
        intro n hn
        obtain ⟨hnf, hn2, hnO⟩ := Finset.mem_filter.mp hn
        have hb := dyadic_fiber_mem_bounds 1 N j n hnf
        have h2j : (((2:ℕ) ^ j : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hb.1
        have h2jR : (((2:ℕ) ^ j : ℕ) : ℝ) = (2:ℝ) ^ j := by push_cast; ring
        rw [h2jR] at h2j
        have h2le : (2:ℝ) ≤ (2:ℝ) ^ j := by
          calc (2:ℝ) = (2:ℝ) ^ 1 := by norm_num
            _ ≤ (2:ℝ) ^ j := by
                apply pow_le_pow_right₀ (by norm_num) hj
        rw [hImem n hn2 hnO]
        exact inv_mul_log_le ((2:ℝ) ^ j) (n:ℝ) h2le h2j
      have hsum1 := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at hsum1
      have hbpos : (0:ℝ) < 1 / ((2:ℝ) ^ j * Real.log ((2:ℝ) ^ j)) := by
        apply one_div_pos.mpr
        apply mul_pos (by positivity)
        rw [Real.log_pow]
        exact mul_pos (by exact_mod_cast (by omega : 0 < j)) hl2
      have hcast2 : (((2:ℕ) ^ (j + 1) : ℕ) : ℝ) = (2:ℝ) ^ (j + 1) := by
        push_cast
        ring
      have hcard := block_count_le_piK k j N
      rw [hcast2] at hcard
      have hcardR : (((((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
            (fun n => 2 ≤ n ∧ bigOmega n = k)).card : ℕ) : ℝ)
          ≤ (piK k ((2:ℝ) ^ (j + 1)) : ℝ) := by
        exact_mod_cast hcard
      have h4n : (4:ℕ) ≤ 2 ^ (j + 1) := by
        calc (4:ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hx3 : (3:ℝ) ≤ (((2:ℕ) ^ (j + 1) : ℕ) : ℝ) := by
        have h4r : (4:ℝ) ≤ (((2:ℕ) ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h4n
        linarith
      have hpk := hbound (((2:ℕ) ^ (j + 1) : ℕ) : ℝ) hx3
      rw [hcast2] at hpk
      calc ∑ n ∈ ((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
            (fun n => 2 ≤ n ∧ bigOmega n = k), I n
          ≤ (((((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
              (fun n => 2 ≤ n ∧ bigOmega n = k)).card : ℕ) : ℝ) *
              (1 / ((2:ℝ) ^ j * Real.log ((2:ℝ) ^ j))) := hsum1
        _ ≤ (piK k ((2:ℝ) ^ (j + 1)) : ℝ) *
              (1 / ((2:ℝ) ^ j * Real.log ((2:ℝ) ^ j))) :=
            mul_le_mul_of_nonneg_right hcardR hbpos.le
        _ ≤ C * (2:ℝ) ^ (j + 1) * (Real.log (Real.log ((2:ℝ) ^ (j + 1)))) ^ (k - 1) /
              Real.log ((2:ℝ) ^ (j + 1)) * (1 / ((2:ℝ) ^ j * Real.log ((2:ℝ) ^ j))) :=
            mul_le_mul_of_nonneg_right hpk hbpos.le
        _ ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
              (1 / ((j:ℝ) * Real.sqrt j)) :=
            block_arith C hC (k - 1) j hj
    have hKnn : (0:ℝ) ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 :=
      div_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * C)
        (pow_nonneg (by positivity) _)) (by positivity)
    have hpartial : ∀ N : ℕ, ∑ i ∈ Finset.range N, I i
        ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 * 3 := by
      intro N
      have h1 : ∑ i ∈ Finset.range N, I i ≤ ∑ i ∈ Finset.Ioc 1 N, I i := by
        have hzs : ∑ i ∈ (Finset.range N).filter (fun i => 1 < i), I i
            = ∑ i ∈ Finset.range N, I i := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i hi hif
          apply hIvan
          intro hmem
          obtain ⟨h2i, _⟩ := hmem
          exact hif (Finset.mem_filter.mpr ⟨hi, by omega⟩)
        rw [← hzs]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨hir, hi1⟩ := Finset.mem_filter.mp hi
          have hiN := Finset.mem_range.mp hir
          exact Finset.mem_Ioc.mpr ⟨hi1, by omega⟩
        · intro i _ _
          exact hInn i
      have h2 := sum_dyadic_fiberwise 1 N I
      have hfib0 : (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = 0) = (∅ : Finset ℕ) := by
        apply Finset.filter_eq_empty_iff.mpr
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have hlp := Nat.log_pos (by norm_num : 1 < 2) (by omega : 2 ≤ n)
        omega
      have hsplit : Finset.range (Nat.log 2 N + 1)
          = insert 0 (Finset.Icc 1 (Nat.log 2 N)) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      have hIcc3 : ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
          1 / ((j:ℝ) * Real.sqrt j) ≤ 3 := by
        rcases Nat.lt_or_ge (Nat.log 2 N) 1 with hJ0 | hJ1
        · have hemp : Finset.Icc 1 (Nat.log 2 N) = (∅ : Finset ℕ) := by
            apply Finset.Icc_eq_empty
            omega
          rw [hemp, Finset.sum_empty]
          norm_num
        · have hins : Finset.Icc 1 (Nat.log 2 N)
              = insert 1 (Finset.Icc 2 (Nat.log 2 N)) := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          rw [hins, Finset.sum_insert (by simp)]
          have ht := telescope_sqrt (Nat.log 2 N)
          have h11 : (1:ℝ) / (((1:ℕ):ℝ) * Real.sqrt ((1:ℕ):ℝ)) = 1 := by
            simp [Real.sqrt_one]
          rw [h11]
          linarith [ht]
      have hmain : ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
          ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n
            ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 * 3 := by
        calc ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
            ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n
            ≤ ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
              4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
                (1 / ((j:ℝ) * Real.sqrt j)) :=
              Finset.sum_le_sum (fun j hjm => hblock N j (Finset.mem_Icc.mp hjm).1)
          _ = 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
              ∑ j ∈ Finset.Icc 1 (Nat.log 2 N), (1 / ((j:ℝ) * Real.sqrt j)) := by
              rw [Finset.mul_sum]
          _ ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 * 3 :=
              mul_le_mul_of_nonneg_left hIcc3 hKnn
      calc ∑ i ∈ Finset.range N, I i
          ≤ ∑ i ∈ Finset.Ioc 1 N, I i := h1
        _ = ∑ j ∈ Finset.range (Nat.log 2 N + 1),
            ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n := h2
        _ = ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = 0), I n
            + ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
                ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n := by
            rw [hsplit, Finset.sum_insert (by simp)]
        _ = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N),
              ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n := by
            rw [hfib0]
            simp
        _ ≤ _ := hmain
    exact summable_of_sum_range_le hInn hpartial
  exact (summable_subtype_iff_indicator
    (s := {n : ℕ | 2 ≤ n ∧ bigOmega n = k})
    (f := fun n : ℕ => 1 / ((n:ℝ) * Real.log n))).mpr hind

theorem erdos_sums_increase_from_six
    (hnum : NumericalFacts) :
    ∀ k : ℕ, 6 ≤ k → f k < f (k + 1) := by
  sorry

end
