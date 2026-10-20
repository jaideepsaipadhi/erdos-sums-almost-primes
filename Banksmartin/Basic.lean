import Mathlib
import Banksmartin.EulerGamma

-- The `first | ... | ...` combinators in this file carry deliberate fallback
-- branches so the proofs survive Mathlib changes in which branch fires.  The
-- linter flags alternatives the current Mathlib does not reach; that is
-- expected, and removing them would make the file brittle.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

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

/-- MANUSCRIPT section 2.1: Crit(k) = a1(k^2 - 2k - 1) + 2E(k) - E(k+1). -/
noncomputable def Crit (aa : ℝ) (k : ℕ) : ℝ :=
  aa * ((k : ℝ) ^ 2 - 2 * k - 1) + 2 * E aa k - E aa (k + 1)

/-- MANUSCRIPT Theorem 4.1 uniform form / section 7:
D(m) = (log 2) m log(m+1) + 1, the bound with |delta_m| <= D(m). -/
noncomputable def DBound (m : ℕ) : ℝ :=
  Real.log 2 * (m : ℝ) * Real.log ((m : ℝ) + 1) + 1

/-- MANUSCRIPT section 7: R(k), the total of the certified source bounds. -/
noncomputable def RBound (Umax Vmax Sstar alph : ℝ) (k : ℕ) : ℝ :=
  (Real.log 2 / 4) * ((2 * (k : ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax)
    + Sstar * (2 * DBound k + DBound (k + 1))
    + alph * (3 * (k : ℝ) + 4)
    + 3 * (1.45 / (k : ℝ) + 1e-3)

/-- MANUSCRIPT Theorem 7.1: phi(k) = a1(k^2 - 2k - 1) - R(k), the certified
lower bound on Crit(k). -/
noncomputable def phiBound (aa Umax Vmax Sstar alph : ℝ) (k : ℕ) : ℝ :=
  aa * ((k : ℝ) ^ 2 - 2 * (k : ℝ) - 1) - RBound Umax Vmax Sstar alph k

/-- Crit(k) >= phi(k), given the certified bound on the total error sources.
The hypothesis hE bundles the four bullets of section 7 (convolution, S3, S1,
Eexp) into a single bound on |2E(k) - E(k+1)|; each is certified separately in
the manuscript. -/
theorem crit_ge_phi (aa Umax Vmax Sstar alph : ℝ) (k : ℕ)
    (hE : |2 * E aa k - E aa (k + 1)| ≤ RBound Umax Vmax Sstar alph k) :
    phiBound aa Umax Vmax Sstar alph k ≤ Crit aa k := by
  unfold phiBound Crit
  have h := abs_le.mp hE
  linarith [h.1]

/-- D is nonnegative. -/
theorem DBound_nonneg (m : ℕ) : 0 ≤ DBound m := by
  unfold DBound
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hlog : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have hprod : (0 : ℝ) ≤ Real.log 2 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
    apply mul_nonneg (mul_nonneg (le_of_lt hlog2) hm) hlog
  linarith

/-- D is monotone in m. -/
theorem DBound_mono (m : ℕ) : DBound m ≤ DBound (m + 1) := by
  unfold DBound
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hlogmono : Real.log ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1 + 1) := by
    apply Real.log_le_log (by linarith)
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have hstep : Real.log 2 * (m : ℝ) * Real.log ((m : ℝ) + 1)
      ≤ Real.log 2 * ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1 + 1) := by
    apply mul_le_mul _ hlogmono hlognn
    · apply mul_nonneg (le_of_lt hlog2)
      linarith
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hlog2)
    linarith
  linarith

/-- MANUSCRIPT section 2.1: Crit(k) > 0 gives f_k < f_(k+1).
This is the criterion every range of Theorem 1.1 goes through. -/
theorem crit_pos_iff (aa : ℝ) (k : ℕ) :
    0 < Crit aa k → f k < f (k + 1) := by
  intro hpos
  have hcrit := criterion aa k
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℝ) - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hd : 0 < f (k + 1) - f k := by
    rw [hcrit]
    exact mul_pos h2 hpos
  linarith

/-- MANUSCRIPT Theorem 7.1: Crit(k) > 0, hence f_k < f_(k+1), for all k >= k1.

phi(k1) > 0 and the monotonicity of phi are certified in the manuscript
(an Arb ball scan at k1 = 2440, and the derivative gap
a1(2k-2) - [2q Umax + 3 Sstar log2 (log(k+2)+1) + 3 alpha] > 0 increasing by
convexity).  Both enter as hypotheses, as the other certified facts do. -/
theorem theorem_7_1 (aa Umax Vmax Sstar alph : ℝ) (k1 : ℕ)
    (hphi1 : 0 < phiBound aa Umax Vmax Sstar alph k1)
    (hmono : ∀ m : ℕ, k1 ≤ m →
      phiBound aa Umax Vmax Sstar alph m ≤ phiBound aa Umax Vmax Sstar alph (m + 1))
    (hE : ∀ m : ℕ, k1 ≤ m →
      |2 * E aa m - E aa (m + 1)| ≤ RBound Umax Vmax Sstar alph m)
    (k : ℕ) (hk : k1 ≤ k) :
    f k < f (k + 1) := by
  have hphi : ∀ m : ℕ, k1 ≤ m → 0 < phiBound aa Umax Vmax Sstar alph m := by
    intro m hm
    induction m with
    | zero =>
      have : k1 = 0 := Nat.le_zero.mp hm
      rw [this] at hphi1
      exact hphi1
    | succ n ih =>
      rcases Nat.lt_or_ge k1 (n + 1) with h | h
      · have hn : k1 ≤ n := Nat.lt_succ_iff.mp h
        exact lt_of_lt_of_le (ih hn) (hmono n hn)
      · have : k1 = n + 1 := le_antisymm hm h
        rw [this] at hphi1
        exact hphi1
  exact crit_pos_iff aa k (lt_of_lt_of_le (hphi k hk) (crit_ge_phi aa Umax Vmax Sstar alph k (hE k hk)))

/-! ### phi is monotone above 2440 -- a lemma, not a numerical fact

`phiBound k = aa (k^2 - 2k - 1) - RBound k`, and `RBound` is linear in `k` plus
`Sstar` times `DBound` terms plus a positive decreasing tail.  Nothing in it
mentions a prime, a contour or a limit, so the `phi_mono` field of
`NumericalFacts` / `NumericalFactsFull` is derivable rather than assumed.  The
only input not already in those structures is an upper bound on `Umax`, which
the manuscript states as `|U| <= 0.08436`.  `Vmax` enters `RBound` only as
`+ 2 Vmax`, constant in `k`, so it cancels from the difference and is not
needed here at all.

The argument is the one `numerics/bm-rebuild-v21/k1_far_range.py` runs in Arb
at lines 89-92: the quadratic's increment `aa (2m-1)` outruns `RBound`'s, which
is `O(log m)`.
-/

/-- `log (x+1) - log x <= 1/x` for `x > 0`. -/
theorem log_succ_sub_le_inv (x : ℝ) (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (x + 1) / x by positivity)
  rw [Real.log_div (ne_of_gt hx1) (ne_of_gt hx)] at h
  have he : (x + 1) / x - 1 = 1 / x := by
    field_simp
    try ring
  rw [he] at h
  exact h

/-- The second difference of `DBound` grows only logarithmically. -/
theorem DBound_second_diff_le (m : ℕ) (hm : 1 ≤ m) :
    DBound (m + 1) + DBound (m + 2) - 2 * DBound m
      ≤ Real.log 2 * (4 + 3 * Real.log ((m : ℝ) + 3)) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have h1 : (0:ℝ) < (m:ℝ) + 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log ((m:ℝ) + 2) ≤ Real.log ((m:ℝ) + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hgap : Real.log ((m:ℝ) + 3) - Real.log ((m:ℝ) + 1) ≤ 2 / ((m:ℝ) + 1) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < ((m:ℝ) + 3) / ((m:ℝ) + 1) by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at h
    have he : ((m:ℝ) + 3) / ((m:ℝ) + 1) - 1 = 2 / ((m:ℝ) + 1) := by
      field_simp
      try ring
    rw [he] at h
    exact h
  have hmul : 2 * (m:ℝ) * (2 / ((m:ℝ) + 1)) ≤ 4 := by
    have hr : 2 * (m:ℝ) * (2 / ((m:ℝ) + 1)) = 4 * (m:ℝ) / ((m:ℝ) + 1) := by
      field_simp; ring
    rw [hr, div_le_iff₀ h1]
    linarith
  have hA : ((m:ℝ) + 1) * Real.log ((m:ℝ) + 2)
              ≤ ((m:ℝ) + 1) * Real.log ((m:ℝ) + 3) :=
    mul_le_mul_of_nonneg_left hL2 (by linarith)
  have hB : 2 * (m:ℝ) * (Real.log ((m:ℝ) + 3) - Real.log ((m:ℝ) + 1))
              ≤ 2 * (m:ℝ) * (2 / ((m:ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hgap (by linarith)
  have hbracket :
      ((m:ℝ) + 1) * Real.log ((m:ℝ) + 2) + ((m:ℝ) + 2) * Real.log ((m:ℝ) + 3)
        - 2 * (m:ℝ) * Real.log ((m:ℝ) + 1)
      ≤ 4 + 3 * Real.log ((m:ℝ) + 3) := by
    linarith [hA, hB, hmul]
  have hscaled := mul_le_mul_of_nonneg_left hbracket hlog2.le
  simp only [DBound]
  push_cast
  try simp only [show ((m:ℝ) + 1) + 1 = (m:ℝ) + 2 from by ring,
                 show ((m:ℝ) + 2) + 1 = (m:ℝ) + 3 from by ring]
  nlinarith [hscaled]

/-- `log 2441 <= 7.8165136`, from `2441 = 2048 * (2441/2048)` and
`log (1+x) <= x`.  The cruder `log 2441 <= 12 log 2 = 8.318` is far too lossy
here: it would push `RBound 2440` above the quadratic and the criterion would
not close. -/
theorem log_2441_le : Real.log 2441 ≤ 7.8165136 := by
  have hsplit : Real.log (2441:ℝ) = Real.log 2048 + Real.log (2441/2048) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2048 : Real.log (2048:ℝ) = 11 * Real.log 2 := by
    rw [show (2048:ℝ) = 2 ^ (11:ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hfrac : Real.log ((2441:ℝ)/2048) ≤ 2441/2048 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hsplit, h2048]
  linarith [hfrac, hl2]

/-- `log 2442 <= 7.8170019`, the same way. -/
theorem log_2442_le : Real.log 2442 ≤ 7.8170019 := by
  have hsplit : Real.log (2442:ℝ) = Real.log 2048 + Real.log (2442/2048) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2048 : Real.log (2048:ℝ) = 11 * Real.log 2 := by
    rw [show (2048:ℝ) = 2 ^ (11:ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hfrac : Real.log ((2442:ℝ)/2048) ≤ 2442/2048 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hsplit, h2048]
  linarith [hfrac, hl2]

theorem DBound_2440_le : DBound 2440 ≤ 13222 := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl20 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfold : Real.log ((2440:ℝ) + 1) = Real.log 2441 := by norm_num
  have hb0 : (0:ℝ) ≤ Real.log 2441 := Real.log_nonneg (by norm_num)
  have ha : Real.log 2 * 2440 ≤ 0.6931471808 * 2440 := by linarith
  have hmul : Real.log 2 * 2440 * Real.log 2441
                ≤ 0.6931471808 * 2440 * 7.8165136 :=
    mul_le_mul ha log_2441_le hb0 (by norm_num)
  simp only [DBound]
  push_cast
  try norm_num
  linarith [hmul, hfold]

theorem DBound_2441_le : DBound 2441 ≤ 13228 := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl20 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfold : Real.log ((2441:ℝ) + 1) = Real.log 2442 := by norm_num
  have hb0 : (0:ℝ) ≤ Real.log 2442 := Real.log_nonneg (by norm_num)
  have ha : Real.log 2 * 2441 ≤ 0.6931471808 * 2441 := by linarith
  have hmul : Real.log 2 * 2441 * Real.log 2442
                ≤ 0.6931471808 * 2441 * 7.8170019 :=
    mul_le_mul ha log_2442_le hb0 (by norm_num)
  simp only [DBound]
  push_cast
  try norm_num
  linarith [hmul, hfold]

/-- `phi_at_k1` as a theorem: `phi(2440) > 0` from the parameter bounds.
Needs an upper bound on `Vmax` as well as on `Umax`; the manuscript states
both (`0.08436` and `1.90747`).  The margin is about 418 out of 390236, a
tenth of a percent, so the `log 2441` bound above has to be the sharp one. -/
theorem phiBound_pos_at_2440 (aa Umax Vmax Sstar alph : ℝ)
    (haa : (0.0656 : ℝ) ≤ aa)
    (hU0 : 0 ≤ Umax) (hU : Umax ≤ 0.08436)
    (hV0 : 0 ≤ Vmax) (hV : Vmax ≤ 1.90747)
    (hS0 : 0 ≤ Sstar) (hS : Sstar ≤ 6.9764)
    (hal0 : 0 ≤ alph) (hal : alph ≤ 15.4257) :
    0 < phiBound aa Umax Vmax Sstar alph 2440 := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl20 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hD1 := DBound_2440_le
  have hD2 := DBound_2441_le
  have hD10 : (0:ℝ) ≤ DBound 2440 := DBound_nonneg 2440
  have hD20 : (0:ℝ) ≤ DBound 2441 := DBound_nonneg 2441
  have hfoldD : DBound (2440 + 1) = DBound 2441 := by norm_num
  have hinner0 : (0:ℝ) ≤ (2 * (2440:ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax := by
    nlinarith [hU0, hV0]
  have hinner : (2 * (2440:ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax
                  ≤ 4878 * 0.08436 + 2 * 1.90747 + 4 * 0.08436 := by
    nlinarith [hU, hV, hU0, hV0]
  have hq4 : Real.log 2 / 4 ≤ 0.6931471808 / 4 := by linarith
  have hq40 : (0:ℝ) ≤ Real.log 2 / 4 := by linarith
  have ht1 : Real.log 2 / 4 * ((2 * (2440:ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax)
               ≤ 73 := by
    have := mul_le_mul hq4 hinner hinner0 (by norm_num)
    nlinarith [this]
  have hsum : 2 * DBound 2440 + DBound 2441 ≤ 2 * 13222 + 13228 := by linarith
  have hsum0 : (0:ℝ) ≤ 2 * DBound 2440 + DBound 2441 := by linarith
  have ht2 : Sstar * (2 * DBound 2440 + DBound 2441) ≤ 276769 := by
    have := mul_le_mul hS hsum hsum0 (by norm_num)
    nlinarith [this]
  have ht3 : alph * (3 * (2440:ℝ) + 4) ≤ 112979 := by nlinarith [hal]
  have hq : (390235:ℝ) ≤ aa * ((2440:ℝ) ^ 2 - 2 * 2440 - 1) := by nlinarith [haa]
  simp only [phiBound, RBound]
  push_cast
  try norm_num
  nlinarith [ht1, ht2, ht3, hq, hfoldD, hD1, hD2]

/-- `phi_mono` as a theorem.  The hypotheses are the bounds the structures
already carry, plus `hU`, which the manuscript states and they do not. -/
theorem phiBound_mono_of_bounds (aa Umax Vmax Sstar alph : ℝ)
    (haa : (0.0656 : ℝ) ≤ aa)
    (hU0 : 0 ≤ Umax) (hU : Umax ≤ 0.08436)
    (hS0 : 0 ≤ Sstar) (hS : Sstar ≤ 6.9764)
    (hal0 : 0 ≤ alph) (hal : alph ≤ 15.4257)
    (m : ℕ) (hm : 2440 ≤ m) :
    phiBound aa Umax Vmax Sstar alph m
      ≤ phiBound aa Umax Vmax Sstar alph (m + 1) := by
  have hlog2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2l : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2 : (0:ℝ) < Real.log 2 := by linarith
  -- the key inequality, by induction from 2440
  have key : ∀ n : ℕ, 2440 ≤ n →
      Real.log 2 / 2 * Umax
        + Sstar * (Real.log 2 * (4 + 3 * Real.log ((n:ℝ) + 3)))
        + 3 * alph
      ≤ aa * (2 * (n:ℝ) - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have h4096 : Real.log ((2440:ℝ) + 3) ≤ 12 * Real.log 2 := by
          have h1 : Real.log ((2440:ℝ) + 3) ≤ Real.log 4096 :=
            Real.log_le_log (by norm_num) (by norm_num)
          have h2 : Real.log (4096:ℝ) = 12 * Real.log 2 := by
            rw [show (4096:ℝ) = 2 ^ (12:ℕ) by norm_num, Real.log_pow]
            push_cast; ring
          linarith
        have hlogpos : (0:ℝ) ≤ Real.log ((2440:ℝ) + 3) :=
          Real.log_nonneg (by norm_num)
        have hb1 : Real.log 2 / 2 * Umax ≤ 0.6931471808 / 2 * 0.08436 :=
          mul_le_mul (by linarith) hU hU0 (by norm_num)
        -- (2440:R)+3 and 2443 are the same number but different atoms, and
        -- whether the goal carries the folded or the unfolded form depends on
        -- what norm_num did to it.  Bridge them explicitly so linarith can
        -- identify the two either way.
        have hfold : Real.log ((2440:ℝ) + 3) = Real.log 2443 := by norm_num
        have h4096' : Real.log 2443 ≤ 12 * Real.log 2 := by
          rw [← hfold]; exact h4096
        have hlogpos' : (0:ℝ) ≤ Real.log 2443 := by rw [← hfold]; exact hlogpos
        have hinner : (4:ℝ) + 3 * Real.log 2443
                        ≤ 4 + 36 * 0.6931471808 := by
          linarith [h4096', hlog2u]
        have hinner0 : (0:ℝ) ≤ 4 + 3 * Real.log 2443 := by linarith
        have hb2a : Real.log 2 * (4 + 3 * Real.log 2443)
                      ≤ 0.6931471808 * (4 + 36 * 0.6931471808) :=
          mul_le_mul (by linarith) hinner hinner0 (by norm_num)
        have hb2b : (0:ℝ) ≤ Real.log 2 * (4 + 3 * Real.log 2443) :=
          mul_nonneg hlog2.le hinner0
        have hb2 : Sstar * (Real.log 2 * (4 + 3 * Real.log 2443))
                     ≤ 6.9764 * (0.6931471808 * (4 + 36 * 0.6931471808)) :=
          mul_le_mul hS hb2a hb2b (by norm_num)
        push_cast
        try norm_num
        try rw [hfold]
        nlinarith [hb1, hb2, hal, haa, hfold, hlogpos, hlogpos']
    | succ p hp ih =>
        have hp3 : (0:ℝ) < (p:ℝ) + 3 := by positivity
        have hpge : (2440:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
        have hstep : Real.log ((p:ℝ) + 4) - Real.log ((p:ℝ) + 3) ≤ 1 / ((p:ℝ) + 3) := by
          have := log_succ_sub_le_inv ((p:ℝ) + 3) hp3
          simpa [show ((p:ℝ) + 3) + 1 = (p:ℝ) + 4 from by ring] using this
        have hsmall : 1 / ((p:ℝ) + 3) ≤ 1 / 2443 := by
          apply one_div_le_one_div_of_le (by norm_num)
          linarith
        have hSlog : Sstar * Real.log 2 ≤ 6.9764 * 0.6931471808 :=
          mul_le_mul hS (by linarith) hlog2.le (by norm_num)
        have hSL0 : (0:ℝ) ≤ Sstar * Real.log 2 := mul_nonneg hS0 hlog2.le
        have hD0 : (0:ℝ) ≤ Real.log ((p:ℝ) + 4) - Real.log ((p:ℝ) + 3) := by
          have := Real.log_le_log (show (0:ℝ) < (p:ℝ) + 3 by positivity)
            (show ((p:ℝ) + 3) ≤ (p:ℝ) + 4 by linarith)
          linarith
        have hDle : Real.log ((p:ℝ) + 4) - Real.log ((p:ℝ) + 3) ≤ 1 / 2443 := by
          linarith [hstep, hsmall]
        have hprod : (Sstar * Real.log 2)
                       * (Real.log ((p:ℝ) + 4) - Real.log ((p:ℝ) + 3))
                     ≤ (6.9764 * 0.6931471808) * (1 / 2443) :=
          mul_le_mul hSlog hDle hD0 (by norm_num)
        push_cast
        push_cast at ih
        -- push_cast leaves the argument as (p:R) + 1 + 3; hprod speaks of
        -- (p:R) + 4.  Same number, different atom, and linarith compares
        -- atoms, so normalise first or the two never meet.
        try simp only [show ((p:ℝ) + 1 + 3) = (p:ℝ) + 4 from by ring]
        try ring_nf
        try ring_nf at ih hprod
        nlinarith [ih, hprod, haa]
  -- assemble
  have hD := DBound_second_diff_le m (by omega)
  have hkey := key m hm
  have hm0 : (0:ℝ) < (m:ℝ) := by
    have : (2440:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  have hm1 : (0:ℝ) < (m:ℝ) + 1 := by linarith
  have htail : 3 * (1.45 / ((m:ℝ) + 1) + 1e-3) ≤ 3 * (1.45 / (m:ℝ) + 1e-3) := by
    have : (1.45:ℝ) / ((m:ℝ) + 1) ≤ 1.45 / (m:ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hm0 (by linarith)
    linarith
  simp only [phiBound, RBound]
  push_cast
  try simp only [show ((m:ℝ) + 1) + 1 = (m:ℝ) + 2 from by ring]
  nlinarith [hkey, hD, htail, hS0, mul_le_mul_of_nonneg_left hD hS0]

lemma B_nonneg (j : ℕ) (u : ℝ) :
    0 ≤ (2 : ℝ) ^ (-(j : ℝ) * Real.exp (-u)) - 1 + j * Real.log 2 * Real.exp (-u) := by
  set x : ℝ := (j : ℝ) * Real.log 2 * Real.exp (-u) with hx
  have hx0 : 0 ≤ x := by positivity
  have h : (2 : ℝ) ^ (-(j : ℝ) * Real.exp (-u)) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
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
d = (1 / 4) * prod_{p > 2} (1 - 2/p)^(-1) (1 - 1/p)^2 = 0.37869...
Defined as the genuine Euler product (tprod over primes; factors at p = 2
are set to 1). The numerical enclosure is carried by NumericalFacts. -/
noncomputable def dConst : ℝ :=
  (1 / 4) * ∏' p : Nat.Primes,
    (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1)

/-- Nat.Primes is definitionally {p : N // p.Prime}, but Lean treats the two
spellings as distinct for instance resolution.  This equiv (and the transport
lemma below) let products move between them once, rather than needing a bespoke
equiv at each site. -/
def primesEquivSubtype : Nat.Primes ≃ {p : ℕ // p.Prime} where
  toFun p := ⟨ p.1, p.2 ⟩
  invFun p := ⟨ p.1, p.2 ⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- Restricting the equiv to a threshold condition. -/
def primesEquivSubtypeGE (k : ℕ) :
    {p : Nat.Primes // k ≤ (p : ℕ)} ≃ {p : ℕ // p.Prime ∧ k ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2, q.2 ⟩
  invFun q := ⟨ ⟨ q.1, q.2.1 ⟩, q.2.2 ⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

/-- The `if 2 < p` in dConst is the indicator of {p >= 3} (for primes). -/
theorem dConst_if_eq_indicator :
    (fun p : Nat.Primes =>
        (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1))
      = Set.mulIndicator {p : Nat.Primes | (3 : ℕ) ≤ (p : ℕ)}
          (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2) := by
  funext p
  by_cases h : p ∈ {q : Nat.Primes | (3 : ℕ) ≤ (q : ℕ)}
  · have h3 : (3 : ℕ) ≤ (p : ℕ) := h
    rw [Set.mulIndicator_of_mem h, if_pos (by omega)]
  · have h3 : ¬((3 : ℕ) ≤ (p : ℕ)) := h
    rw [Set.mulIndicator_of_notMem h, if_neg (by omega)]

/-- D4: dConst's indicator product over all primes equals the p >= 3 subtype
product, in the spelling G2C and cFac use. -/
theorem dConst_prod_eq_subtype :
    (∏' p : Nat.Primes,
        (if 2 < (p : ℕ) then (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 else 1))
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 := by
  rw [dConst_if_eq_indicator]
  rw [← tprod_subtype {p : Nat.Primes | (3 : ℕ) ≤ (p : ℕ)}
    (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)]
  exact (primesEquivSubtypeGE 3).tprod_eq
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)

/-- The real regularised family at z = 2 is multipliable over p >= 3.
Exact algebra: (1-2/p)^(-1)(1-1/p)^2 - 1 = 1/(p(p-2)) <= 3/p^2 for p >= 3.
Without this, dConst would be an assertion about a tprod junk value. -/
theorem dConst_family_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2) := by
  have hexact : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 - 1
        = 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) := by
    intro p
    have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hp2 : (0 : ℝ) < ((p : ℕ) : ℝ) - 2 := by linarith
    have hne : (1 : ℝ) - 2 / ((p : ℕ) : ℝ) ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      field_simp at hcon
      linarith
    field_simp
    ring
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      3 * (1 / ((p : ℕ) : ℝ) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
      simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    exact (hbase.subtype _).mul_left 3
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 - 1) := by
    apply Summable.of_nonneg_of_le _ _ hcomp
    · intro p
      rw [hexact p]
      have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
      have : (0 : ℝ) < ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2) := by nlinarith
      positivity
    · intro p
      rw [hexact p]
      have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
      have hden : (0 : ℝ) < ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2) := by nlinarith
      rw [show (3 : ℝ) * (1 / ((p : ℕ) : ℝ) ^ 2) = 3 / ((p : ℕ) : ℝ) ^ 2 by ring]
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
  have h := Real.multipliable_one_add_of_summable hsum
  apply h.congr
  intro p
  ring

/-- The complex product of casts at z = 2 is the cast of the real product. -/
theorem dConst_prod_ofReal :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        ((((1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ))
      = (((∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
  exact (dConst_family_multipliable.map_tprod Complex.ofRealHom Complex.continuous_ofReal).symm

/-- The secondary-term constant a1 = d * log 2 / 4 from GLW Theorem 2:
f_k = 1 - 2^(-k) (a1 k^2 + O(k log(k+1))). -/
noncomputable def aOneConst : ℝ := dConst * Real.log 2 / 4
/-- Manuscript Lemma 3.6: rho = Res_{z=3} G2(1,z)
      = -(1 / 9) * prod_{p >= 5} (1 - 3/p)^(-1) (1 - 1/p)^3 = -0.1749323...
Same Euler-product convention as dConst (factors below the threshold set
to 1).  Previously a bare literal, which left rho_enclosure vacuous. -/
noncomputable def rhoConst : ℝ :=
  -(1 / 9) * ∏' p : Nat.Primes,
    (if 5 ≤ (p : ℕ) then (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 else 1)
/-- MANUSCRIPT section 3.4: S* = sum_{i>=0} 2^i |c_i|, the unsigned bound
constant for the convolution Delta(k).

A LITERAL, by necessity: cCoeff is defined thousands of lines below, so the
series cannot be written here.  `SstarValue`, defined after cCoeff, IS that
series, and `SstarValue_summable` proves it converges given Lemma 3.7's Cauchy
tail.  The two are deliberately NOT identified: SstarConst is the certified
numeric value, SstarValue the mathematical object it encloses, and the
enclosure is one of the things NumericalFacts assumes.  The final theorems take
S* as a parameter with its bound, so neither constant is load-bearing on its
own. -/
noncomputable def SstarConst : ℝ := 6.9764

/-- MANUSCRIPT section 3.5: alpha_+ is the constant in B_1(k) <= alpha_+ (k+1).

A LITERAL BY DESIGN, not an omission.  alpha_+ = (1 / 2) sum_i beta_i 2^i where
beta_i = max_{s in [1,2]} |[z^i] G2^(1,0)(s,z)|, evaluated by a 1600-box
interval sweep in Arb.  It is the output of a certified computation, not a
quantity Lean can define and evaluate.  E1k_le_alpha takes it as a parameter
with its bounding hypothesis, which is the honest treatment.

This records the manuscript's value.  The regenerated sweep gives 15.4257,
which is what NumericalFacts.alpha_bound carries; this definition is not
referenced. -/
noncomputable def alphaConst : ℝ := 15.5716

/-- MANUSCRIPT Theorem 6.1: Gamma = (1 / 2) sum_{i>=1} gammahat_i 2^i, the
k-independent remainder bound.

A LITERAL BY DESIGN, as alphaConst is.  gammahat_i = max_{s in [1,2]}
|[z^i] G2^(2,0)(s,z)|, evaluated by an 800-box interval sweep in Arb using the
closed form G2^(2,0) = G2(z^2 c^2 + z c') -- which IS proved here, as
hasDerivAt_G2manu_second.  theorem_6_1 takes Gamma as a parameter with its
bounding hypothesis.

The k-INDEPENDENCE of Gamma, which is what makes the refinement work, is
proved: it is geom_two_three, sum_l 2^l 3^(-l-1) = 1.

This records the manuscript's value.  The regenerated sweep gives 104.5196,
which is what NumericalFacts.Gamma_bound carries; this definition is not
referenced. -/
noncomputable def GammaConst : ℝ := 105.41

/-- `aOneConst = dConst * log 2 / 4 >= 0.0656`, from the certified `d`. -/
theorem aOneConst_ge_of_d (h : |(0.3786950 : ℝ) - dConst| ≤ 5.3e-8) :
    (0.0656 : ℝ) ≤ aOneConst := by
  have hb := abs_le.mp h
  have hd : (0.37869494 : ℝ) ≤ dConst := by linarith [hb.1, hb.2]
  have hprod : (0.37869494 : ℝ) * 0.6931471803 ≤ dConst * Real.log 2 :=
    mul_le_mul hd Real.log_two_gt_d9.le (by norm_num) (by linarith)
  unfold aOneConst
  linarith [hprod]

/-- Partial products bound an infinite product from below when every factor is
at least 1.  Mathlib has no `Finset.prod_le_hasProd` -- the multiplicative
order lemmas want an `OrderedCommMonoid`, which ℝ is not under multiplication
-- so this is proved from the net definition directly: for any finite `t`
containing `s`, the product over `t` splits as (product over `t \ s`) times
(product over `s`), and the first factor is at least 1. -/
theorem prod_le_hasProd_of_one_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (a : ℝ)
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

/-- The dConst Euler factor, in closed form.  This is the `hexact` step of
`dConst_family_multipliable` stated on its own:

    (1 - 2/p)⁻¹ (1 - 1/p)² = (p-1)²/(p(p-2)) = 1 + 1/(p(p-2)).

Rational in `p`, with no logarithm anywhere -- which is why a lower bound on
dConst is reachable in the kernel while the two-sided enclosure is not. -/
theorem dConst_factor_sub_one (p : ℕ) (hp : 3 ≤ p) :
    (1 - 2 / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) ^ 2 - 1
      = 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hne : (1 : ℝ) - 2 / (p : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hcon
    field_simp at hcon
    linarith
  field_simp
  ring

/-- Every dConst factor is at least 1, since 1/(p(p-2)) > 0 for p ≥ 3. -/
theorem dConst_factor_one_le (p : ℕ) (hp : 3 ≤ p) :
    (1 : ℝ) ≤ (1 - 2 / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
  have hpos : (0 : ℝ) < 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by positivity
  have := dConst_factor_sub_one p hp
  linarith

/-- The 94 primes 3 ≤ p ≤ 499, as a `Finset` of the p ≥ 3 prime subtype. -/
def dLowerSet : Finset {p : ℕ // p.Prime ∧ 3 ≤ p} :=
  {
      ⟨3, by norm_num⟩, ⟨5, by norm_num⟩, ⟨7, by norm_num⟩, ⟨11, by norm_num⟩, ⟨13, by
      norm_num⟩, ⟨17, by norm_num⟩, ⟨19, by norm_num⟩, ⟨23, by norm_num⟩, ⟨29, by
      norm_num⟩, ⟨31, by norm_num⟩, ⟨37, by norm_num⟩, ⟨41, by norm_num⟩, ⟨43, by
      norm_num⟩, ⟨47, by norm_num⟩, ⟨53, by norm_num⟩, ⟨59, by norm_num⟩, ⟨61, by
      norm_num⟩, ⟨67, by norm_num⟩, ⟨71, by norm_num⟩, ⟨73, by norm_num⟩, ⟨79, by
      norm_num⟩, ⟨83, by norm_num⟩, ⟨89, by norm_num⟩, ⟨97, by norm_num⟩, ⟨101, by
      norm_num⟩, ⟨103, by norm_num⟩, ⟨107, by norm_num⟩, ⟨109, by norm_num⟩, ⟨113, by
      norm_num⟩, ⟨127, by norm_num⟩, ⟨131, by norm_num⟩, ⟨137, by norm_num⟩, ⟨139, by
      norm_num⟩, ⟨149, by norm_num⟩, ⟨151, by norm_num⟩, ⟨157, by norm_num⟩, ⟨163, by
      norm_num⟩, ⟨167, by norm_num⟩, ⟨173, by norm_num⟩, ⟨179, by norm_num⟩, ⟨181, by
      norm_num⟩, ⟨191, by norm_num⟩, ⟨193, by norm_num⟩, ⟨197, by norm_num⟩, ⟨199, by
      norm_num⟩, ⟨211, by norm_num⟩, ⟨223, by norm_num⟩, ⟨227, by norm_num⟩, ⟨229, by
      norm_num⟩, ⟨233, by norm_num⟩, ⟨239, by norm_num⟩, ⟨241, by norm_num⟩, ⟨251, by
      norm_num⟩, ⟨257, by norm_num⟩, ⟨263, by norm_num⟩, ⟨269, by norm_num⟩, ⟨271, by
      norm_num⟩, ⟨277, by norm_num⟩, ⟨281, by norm_num⟩, ⟨283, by norm_num⟩, ⟨293, by
      norm_num⟩, ⟨307, by norm_num⟩, ⟨311, by norm_num⟩, ⟨313, by norm_num⟩, ⟨317, by
      norm_num⟩, ⟨331, by norm_num⟩, ⟨337, by norm_num⟩, ⟨347, by norm_num⟩, ⟨349, by
      norm_num⟩, ⟨353, by norm_num⟩, ⟨359, by norm_num⟩, ⟨367, by norm_num⟩, ⟨373, by
      norm_num⟩, ⟨379, by norm_num⟩, ⟨383, by norm_num⟩, ⟨389, by norm_num⟩, ⟨397, by
      norm_num⟩, ⟨401, by norm_num⟩, ⟨409, by norm_num⟩, ⟨419, by norm_num⟩, ⟨421, by
      norm_num⟩, ⟨431, by norm_num⟩, ⟨433, by norm_num⟩, ⟨439, by norm_num⟩, ⟨443, by
      norm_num⟩, ⟨449, by norm_num⟩, ⟨457, by norm_num⟩, ⟨461, by norm_num⟩, ⟨463, by
      norm_num⟩, ⟨467, by norm_num⟩, ⟨479, by norm_num⟩, ⟨487, by norm_num⟩, ⟨491, by
      norm_num⟩, ⟨499, by norm_num⟩
  }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A certified lower bound on `d`, proved rather than assumed.**

`dConst = (1/4) ∏'_{p ≥ 3} (1 - 2/p)⁻¹(1 - 1/p)²`, every factor of which
exceeds 1 by `dConst_factor_one_le`.  So the product over the finite set
`dLowerSet` is a lower bound for the whole product, and **no tail estimate is
involved at all** -- which is the entire reason this is reachable here, when
the two-sided `5.3e-8` enclosure that the `d_enclosure` field used to
assume is not.

The 94 primes p ≤ 499 give `0.378591358693...`; the true value is `0.3786950`.
What the development needs is `0.3785631789`, from `aOneConst ≥ 0.0656` with
`Real.log_two_gt_d9` in place of the true `log 2`.  Margin `2.8e-5`.

Regenerate the numeral with `numerics/gen_dconst_lower.py`. -/
theorem dConst_lower_bound : (0.3785913 : ℝ) ≤ dConst := by
  have hsub : dConst = (1 / 4) * ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 := by
    unfold dConst
    rw [dConst_prod_eq_subtype]
  have hone : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 : ℝ) ≤ (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 :=
    fun p => dConst_factor_one_le (p : ℕ) p.2.2
  have hpart := prod_le_hasProd_of_one_le dLowerSet
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)
    _ hone dConst_family_multipliable.hasProd
  have heval : (∏ p ∈ dLowerSet,
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)
      ≥ (4 * 0.3785913 : ℝ) := by
    norm_num [dLowerSet, Finset.prod_insert, Finset.mem_insert,
      Finset.mem_singleton, Subtype.mk.injEq]
  rw [hsub]
  linarith [hpart, heval]

/-- `aOneConst ≥ 0.0656`, with no numerical hypothesis.  This is
`aOneConst_ge_of_d` with its assumption discharged by `dConst_lower_bound`. -/
theorem aOneConst_ge : (0.0656 : ℝ) ≤ aOneConst := by
  have hd := dConst_lower_bound
  have hprod : (0.3785913 : ℝ) * 0.6931471803 ≤ dConst * Real.log 2 :=
    mul_le_mul hd Real.log_two_gt_d9.le (by norm_num) (by linarith)
  unfold aOneConst
  linarith [hprod]

set_option maxRecDepth 4000000 in
/-- The 668 primes 3 ≤ p ≤ 4999. -/
def dLowerSetSharp : Finset {p : ℕ // p.Prime ∧ 3 ≤ p} :=
  {
      ⟨3, by norm_num⟩, ⟨5, by norm_num⟩, ⟨7, by norm_num⟩, ⟨11, by norm_num⟩, ⟨13, by
      norm_num⟩, ⟨17, by norm_num⟩, ⟨19, by norm_num⟩, ⟨23, by norm_num⟩, ⟨29, by
      norm_num⟩, ⟨31, by norm_num⟩, ⟨37, by norm_num⟩, ⟨41, by norm_num⟩, ⟨43, by
      norm_num⟩, ⟨47, by norm_num⟩, ⟨53, by norm_num⟩, ⟨59, by norm_num⟩, ⟨61, by
      norm_num⟩, ⟨67, by norm_num⟩, ⟨71, by norm_num⟩, ⟨73, by norm_num⟩, ⟨79, by
      norm_num⟩, ⟨83, by norm_num⟩, ⟨89, by norm_num⟩, ⟨97, by norm_num⟩, ⟨101, by
      norm_num⟩, ⟨103, by norm_num⟩, ⟨107, by norm_num⟩, ⟨109, by norm_num⟩, ⟨113, by
      norm_num⟩, ⟨127, by norm_num⟩, ⟨131, by norm_num⟩, ⟨137, by norm_num⟩, ⟨139, by
      norm_num⟩, ⟨149, by norm_num⟩, ⟨151, by norm_num⟩, ⟨157, by norm_num⟩, ⟨163, by
      norm_num⟩, ⟨167, by norm_num⟩, ⟨173, by norm_num⟩, ⟨179, by norm_num⟩, ⟨181, by
      norm_num⟩, ⟨191, by norm_num⟩, ⟨193, by norm_num⟩, ⟨197, by norm_num⟩, ⟨199, by
      norm_num⟩, ⟨211, by norm_num⟩, ⟨223, by norm_num⟩, ⟨227, by norm_num⟩, ⟨229, by
      norm_num⟩, ⟨233, by norm_num⟩, ⟨239, by norm_num⟩, ⟨241, by norm_num⟩, ⟨251, by
      norm_num⟩, ⟨257, by norm_num⟩, ⟨263, by norm_num⟩, ⟨269, by norm_num⟩, ⟨271, by
      norm_num⟩, ⟨277, by norm_num⟩, ⟨281, by norm_num⟩, ⟨283, by norm_num⟩, ⟨293, by
      norm_num⟩, ⟨307, by norm_num⟩, ⟨311, by norm_num⟩, ⟨313, by norm_num⟩, ⟨317, by
      norm_num⟩, ⟨331, by norm_num⟩, ⟨337, by norm_num⟩, ⟨347, by norm_num⟩, ⟨349, by
      norm_num⟩, ⟨353, by norm_num⟩, ⟨359, by norm_num⟩, ⟨367, by norm_num⟩, ⟨373, by
      norm_num⟩, ⟨379, by norm_num⟩, ⟨383, by norm_num⟩, ⟨389, by norm_num⟩, ⟨397, by
      norm_num⟩, ⟨401, by norm_num⟩, ⟨409, by norm_num⟩, ⟨419, by norm_num⟩, ⟨421, by
      norm_num⟩, ⟨431, by norm_num⟩, ⟨433, by norm_num⟩, ⟨439, by norm_num⟩, ⟨443, by
      norm_num⟩, ⟨449, by norm_num⟩, ⟨457, by norm_num⟩, ⟨461, by norm_num⟩, ⟨463, by
      norm_num⟩, ⟨467, by norm_num⟩, ⟨479, by norm_num⟩, ⟨487, by norm_num⟩, ⟨491, by
      norm_num⟩, ⟨499, by norm_num⟩, ⟨503, by norm_num⟩, ⟨509, by norm_num⟩, ⟨521, by
      norm_num⟩, ⟨523, by norm_num⟩, ⟨541, by norm_num⟩, ⟨547, by norm_num⟩, ⟨557, by
      norm_num⟩, ⟨563, by norm_num⟩, ⟨569, by norm_num⟩, ⟨571, by norm_num⟩, ⟨577, by
      norm_num⟩, ⟨587, by norm_num⟩, ⟨593, by norm_num⟩, ⟨599, by norm_num⟩, ⟨601, by
      norm_num⟩, ⟨607, by norm_num⟩, ⟨613, by norm_num⟩, ⟨617, by norm_num⟩, ⟨619, by
      norm_num⟩, ⟨631, by norm_num⟩, ⟨641, by norm_num⟩, ⟨643, by norm_num⟩, ⟨647, by
      norm_num⟩, ⟨653, by norm_num⟩, ⟨659, by norm_num⟩, ⟨661, by norm_num⟩, ⟨673, by
      norm_num⟩, ⟨677, by norm_num⟩, ⟨683, by norm_num⟩, ⟨691, by norm_num⟩, ⟨701, by
      norm_num⟩, ⟨709, by norm_num⟩, ⟨719, by norm_num⟩, ⟨727, by norm_num⟩, ⟨733, by
      norm_num⟩, ⟨739, by norm_num⟩, ⟨743, by norm_num⟩, ⟨751, by norm_num⟩, ⟨757, by
      norm_num⟩, ⟨761, by norm_num⟩, ⟨769, by norm_num⟩, ⟨773, by norm_num⟩, ⟨787, by
      norm_num⟩, ⟨797, by norm_num⟩, ⟨809, by norm_num⟩, ⟨811, by norm_num⟩, ⟨821, by
      norm_num⟩, ⟨823, by norm_num⟩, ⟨827, by norm_num⟩, ⟨829, by norm_num⟩, ⟨839, by
      norm_num⟩, ⟨853, by norm_num⟩, ⟨857, by norm_num⟩, ⟨859, by norm_num⟩, ⟨863, by
      norm_num⟩, ⟨877, by norm_num⟩, ⟨881, by norm_num⟩, ⟨883, by norm_num⟩, ⟨887, by
      norm_num⟩, ⟨907, by norm_num⟩, ⟨911, by norm_num⟩, ⟨919, by norm_num⟩, ⟨929, by
      norm_num⟩, ⟨937, by norm_num⟩, ⟨941, by norm_num⟩, ⟨947, by norm_num⟩, ⟨953, by
      norm_num⟩, ⟨967, by norm_num⟩, ⟨971, by norm_num⟩, ⟨977, by norm_num⟩, ⟨983, by
      norm_num⟩, ⟨991, by norm_num⟩, ⟨997, by norm_num⟩, ⟨1009, by norm_num⟩, ⟨1013,
      by norm_num⟩, ⟨1019, by norm_num⟩, ⟨1021, by norm_num⟩, ⟨1031, by norm_num⟩,
      ⟨1033, by norm_num⟩, ⟨1039, by norm_num⟩, ⟨1049, by norm_num⟩, ⟨1051, by
      norm_num⟩, ⟨1061, by norm_num⟩, ⟨1063, by norm_num⟩, ⟨1069, by norm_num⟩, ⟨1087,
      by norm_num⟩, ⟨1091, by norm_num⟩, ⟨1093, by norm_num⟩, ⟨1097, by norm_num⟩,
      ⟨1103, by norm_num⟩, ⟨1109, by norm_num⟩, ⟨1117, by norm_num⟩, ⟨1123, by
      norm_num⟩, ⟨1129, by norm_num⟩, ⟨1151, by norm_num⟩, ⟨1153, by norm_num⟩, ⟨1163,
      by norm_num⟩, ⟨1171, by norm_num⟩, ⟨1181, by norm_num⟩, ⟨1187, by norm_num⟩,
      ⟨1193, by norm_num⟩, ⟨1201, by norm_num⟩, ⟨1213, by norm_num⟩, ⟨1217, by
      norm_num⟩, ⟨1223, by norm_num⟩, ⟨1229, by norm_num⟩, ⟨1231, by norm_num⟩, ⟨1237,
      by norm_num⟩, ⟨1249, by norm_num⟩, ⟨1259, by norm_num⟩, ⟨1277, by norm_num⟩,
      ⟨1279, by norm_num⟩, ⟨1283, by norm_num⟩, ⟨1289, by norm_num⟩, ⟨1291, by
      norm_num⟩, ⟨1297, by norm_num⟩, ⟨1301, by norm_num⟩, ⟨1303, by norm_num⟩, ⟨1307,
      by norm_num⟩, ⟨1319, by norm_num⟩, ⟨1321, by norm_num⟩, ⟨1327, by norm_num⟩,
      ⟨1361, by norm_num⟩, ⟨1367, by norm_num⟩, ⟨1373, by norm_num⟩, ⟨1381, by
      norm_num⟩, ⟨1399, by norm_num⟩, ⟨1409, by norm_num⟩, ⟨1423, by norm_num⟩, ⟨1427,
      by norm_num⟩, ⟨1429, by norm_num⟩, ⟨1433, by norm_num⟩, ⟨1439, by norm_num⟩,
      ⟨1447, by norm_num⟩, ⟨1451, by norm_num⟩, ⟨1453, by norm_num⟩, ⟨1459, by
      norm_num⟩, ⟨1471, by norm_num⟩, ⟨1481, by norm_num⟩, ⟨1483, by norm_num⟩, ⟨1487,
      by norm_num⟩, ⟨1489, by norm_num⟩, ⟨1493, by norm_num⟩, ⟨1499, by norm_num⟩,
      ⟨1511, by norm_num⟩, ⟨1523, by norm_num⟩, ⟨1531, by norm_num⟩, ⟨1543, by
      norm_num⟩, ⟨1549, by norm_num⟩, ⟨1553, by norm_num⟩, ⟨1559, by norm_num⟩, ⟨1567,
      by norm_num⟩, ⟨1571, by norm_num⟩, ⟨1579, by norm_num⟩, ⟨1583, by norm_num⟩,
      ⟨1597, by norm_num⟩, ⟨1601, by norm_num⟩, ⟨1607, by norm_num⟩, ⟨1609, by
      norm_num⟩, ⟨1613, by norm_num⟩, ⟨1619, by norm_num⟩, ⟨1621, by norm_num⟩, ⟨1627,
      by norm_num⟩, ⟨1637, by norm_num⟩, ⟨1657, by norm_num⟩, ⟨1663, by norm_num⟩,
      ⟨1667, by norm_num⟩, ⟨1669, by norm_num⟩, ⟨1693, by norm_num⟩, ⟨1697, by
      norm_num⟩, ⟨1699, by norm_num⟩, ⟨1709, by norm_num⟩, ⟨1721, by norm_num⟩, ⟨1723,
      by norm_num⟩, ⟨1733, by norm_num⟩, ⟨1741, by norm_num⟩, ⟨1747, by norm_num⟩,
      ⟨1753, by norm_num⟩, ⟨1759, by norm_num⟩, ⟨1777, by norm_num⟩, ⟨1783, by
      norm_num⟩, ⟨1787, by norm_num⟩, ⟨1789, by norm_num⟩, ⟨1801, by norm_num⟩, ⟨1811,
      by norm_num⟩, ⟨1823, by norm_num⟩, ⟨1831, by norm_num⟩, ⟨1847, by norm_num⟩,
      ⟨1861, by norm_num⟩, ⟨1867, by norm_num⟩, ⟨1871, by norm_num⟩, ⟨1873, by
      norm_num⟩, ⟨1877, by norm_num⟩, ⟨1879, by norm_num⟩, ⟨1889, by norm_num⟩, ⟨1901,
      by norm_num⟩, ⟨1907, by norm_num⟩, ⟨1913, by norm_num⟩, ⟨1931, by norm_num⟩,
      ⟨1933, by norm_num⟩, ⟨1949, by norm_num⟩, ⟨1951, by norm_num⟩, ⟨1973, by
      norm_num⟩, ⟨1979, by norm_num⟩, ⟨1987, by norm_num⟩, ⟨1993, by norm_num⟩, ⟨1997,
      by norm_num⟩, ⟨1999, by norm_num⟩, ⟨2003, by norm_num⟩, ⟨2011, by norm_num⟩,
      ⟨2017, by norm_num⟩, ⟨2027, by norm_num⟩, ⟨2029, by norm_num⟩, ⟨2039, by
      norm_num⟩, ⟨2053, by norm_num⟩, ⟨2063, by norm_num⟩, ⟨2069, by norm_num⟩, ⟨2081,
      by norm_num⟩, ⟨2083, by norm_num⟩, ⟨2087, by norm_num⟩, ⟨2089, by norm_num⟩,
      ⟨2099, by norm_num⟩, ⟨2111, by norm_num⟩, ⟨2113, by norm_num⟩, ⟨2129, by
      norm_num⟩, ⟨2131, by norm_num⟩, ⟨2137, by norm_num⟩, ⟨2141, by norm_num⟩, ⟨2143,
      by norm_num⟩, ⟨2153, by norm_num⟩, ⟨2161, by norm_num⟩, ⟨2179, by norm_num⟩,
      ⟨2203, by norm_num⟩, ⟨2207, by norm_num⟩, ⟨2213, by norm_num⟩, ⟨2221, by
      norm_num⟩, ⟨2237, by norm_num⟩, ⟨2239, by norm_num⟩, ⟨2243, by norm_num⟩, ⟨2251,
      by norm_num⟩, ⟨2267, by norm_num⟩, ⟨2269, by norm_num⟩, ⟨2273, by norm_num⟩,
      ⟨2281, by norm_num⟩, ⟨2287, by norm_num⟩, ⟨2293, by norm_num⟩, ⟨2297, by
      norm_num⟩, ⟨2309, by norm_num⟩, ⟨2311, by norm_num⟩, ⟨2333, by norm_num⟩, ⟨2339,
      by norm_num⟩, ⟨2341, by norm_num⟩, ⟨2347, by norm_num⟩, ⟨2351, by norm_num⟩,
      ⟨2357, by norm_num⟩, ⟨2371, by norm_num⟩, ⟨2377, by norm_num⟩, ⟨2381, by
      norm_num⟩, ⟨2383, by norm_num⟩, ⟨2389, by norm_num⟩, ⟨2393, by norm_num⟩, ⟨2399,
      by norm_num⟩, ⟨2411, by norm_num⟩, ⟨2417, by norm_num⟩, ⟨2423, by norm_num⟩,
      ⟨2437, by norm_num⟩, ⟨2441, by norm_num⟩, ⟨2447, by norm_num⟩, ⟨2459, by
      norm_num⟩, ⟨2467, by norm_num⟩, ⟨2473, by norm_num⟩, ⟨2477, by norm_num⟩, ⟨2503,
      by norm_num⟩, ⟨2521, by norm_num⟩, ⟨2531, by norm_num⟩, ⟨2539, by norm_num⟩,
      ⟨2543, by norm_num⟩, ⟨2549, by norm_num⟩, ⟨2551, by norm_num⟩, ⟨2557, by
      norm_num⟩, ⟨2579, by norm_num⟩, ⟨2591, by norm_num⟩, ⟨2593, by norm_num⟩, ⟨2609,
      by norm_num⟩, ⟨2617, by norm_num⟩, ⟨2621, by norm_num⟩, ⟨2633, by norm_num⟩,
      ⟨2647, by norm_num⟩, ⟨2657, by norm_num⟩, ⟨2659, by norm_num⟩, ⟨2663, by
      norm_num⟩, ⟨2671, by norm_num⟩, ⟨2677, by norm_num⟩, ⟨2683, by norm_num⟩, ⟨2687,
      by norm_num⟩, ⟨2689, by norm_num⟩, ⟨2693, by norm_num⟩, ⟨2699, by norm_num⟩,
      ⟨2707, by norm_num⟩, ⟨2711, by norm_num⟩, ⟨2713, by norm_num⟩, ⟨2719, by
      norm_num⟩, ⟨2729, by norm_num⟩, ⟨2731, by norm_num⟩, ⟨2741, by norm_num⟩, ⟨2749,
      by norm_num⟩, ⟨2753, by norm_num⟩, ⟨2767, by norm_num⟩, ⟨2777, by norm_num⟩,
      ⟨2789, by norm_num⟩, ⟨2791, by norm_num⟩, ⟨2797, by norm_num⟩, ⟨2801, by
      norm_num⟩, ⟨2803, by norm_num⟩, ⟨2819, by norm_num⟩, ⟨2833, by norm_num⟩, ⟨2837,
      by norm_num⟩, ⟨2843, by norm_num⟩, ⟨2851, by norm_num⟩, ⟨2857, by norm_num⟩,
      ⟨2861, by norm_num⟩, ⟨2879, by norm_num⟩, ⟨2887, by norm_num⟩, ⟨2897, by
      norm_num⟩, ⟨2903, by norm_num⟩, ⟨2909, by norm_num⟩, ⟨2917, by norm_num⟩, ⟨2927,
      by norm_num⟩, ⟨2939, by norm_num⟩, ⟨2953, by norm_num⟩, ⟨2957, by norm_num⟩,
      ⟨2963, by norm_num⟩, ⟨2969, by norm_num⟩, ⟨2971, by norm_num⟩, ⟨2999, by
      norm_num⟩, ⟨3001, by norm_num⟩, ⟨3011, by norm_num⟩, ⟨3019, by norm_num⟩, ⟨3023,
      by norm_num⟩, ⟨3037, by norm_num⟩, ⟨3041, by norm_num⟩, ⟨3049, by norm_num⟩,
      ⟨3061, by norm_num⟩, ⟨3067, by norm_num⟩, ⟨3079, by norm_num⟩, ⟨3083, by
      norm_num⟩, ⟨3089, by norm_num⟩, ⟨3109, by norm_num⟩, ⟨3119, by norm_num⟩, ⟨3121,
      by norm_num⟩, ⟨3137, by norm_num⟩, ⟨3163, by norm_num⟩, ⟨3167, by norm_num⟩,
      ⟨3169, by norm_num⟩, ⟨3181, by norm_num⟩, ⟨3187, by norm_num⟩, ⟨3191, by
      norm_num⟩, ⟨3203, by norm_num⟩, ⟨3209, by norm_num⟩, ⟨3217, by norm_num⟩, ⟨3221,
      by norm_num⟩, ⟨3229, by norm_num⟩, ⟨3251, by norm_num⟩, ⟨3253, by norm_num⟩,
      ⟨3257, by norm_num⟩, ⟨3259, by norm_num⟩, ⟨3271, by norm_num⟩, ⟨3299, by
      norm_num⟩, ⟨3301, by norm_num⟩, ⟨3307, by norm_num⟩, ⟨3313, by norm_num⟩, ⟨3319,
      by norm_num⟩, ⟨3323, by norm_num⟩, ⟨3329, by norm_num⟩, ⟨3331, by norm_num⟩,
      ⟨3343, by norm_num⟩, ⟨3347, by norm_num⟩, ⟨3359, by norm_num⟩, ⟨3361, by
      norm_num⟩, ⟨3371, by norm_num⟩, ⟨3373, by norm_num⟩, ⟨3389, by norm_num⟩, ⟨3391,
      by norm_num⟩, ⟨3407, by norm_num⟩, ⟨3413, by norm_num⟩, ⟨3433, by norm_num⟩,
      ⟨3449, by norm_num⟩, ⟨3457, by norm_num⟩, ⟨3461, by norm_num⟩, ⟨3463, by
      norm_num⟩, ⟨3467, by norm_num⟩, ⟨3469, by norm_num⟩, ⟨3491, by norm_num⟩, ⟨3499,
      by norm_num⟩, ⟨3511, by norm_num⟩, ⟨3517, by norm_num⟩, ⟨3527, by norm_num⟩,
      ⟨3529, by norm_num⟩, ⟨3533, by norm_num⟩, ⟨3539, by norm_num⟩, ⟨3541, by
      norm_num⟩, ⟨3547, by norm_num⟩, ⟨3557, by norm_num⟩, ⟨3559, by norm_num⟩, ⟨3571,
      by norm_num⟩, ⟨3581, by norm_num⟩, ⟨3583, by norm_num⟩, ⟨3593, by norm_num⟩,
      ⟨3607, by norm_num⟩, ⟨3613, by norm_num⟩, ⟨3617, by norm_num⟩, ⟨3623, by
      norm_num⟩, ⟨3631, by norm_num⟩, ⟨3637, by norm_num⟩, ⟨3643, by norm_num⟩, ⟨3659,
      by norm_num⟩, ⟨3671, by norm_num⟩, ⟨3673, by norm_num⟩, ⟨3677, by norm_num⟩,
      ⟨3691, by norm_num⟩, ⟨3697, by norm_num⟩, ⟨3701, by norm_num⟩, ⟨3709, by
      norm_num⟩, ⟨3719, by norm_num⟩, ⟨3727, by norm_num⟩, ⟨3733, by norm_num⟩, ⟨3739,
      by norm_num⟩, ⟨3761, by norm_num⟩, ⟨3767, by norm_num⟩, ⟨3769, by norm_num⟩,
      ⟨3779, by norm_num⟩, ⟨3793, by norm_num⟩, ⟨3797, by norm_num⟩, ⟨3803, by
      norm_num⟩, ⟨3821, by norm_num⟩, ⟨3823, by norm_num⟩, ⟨3833, by norm_num⟩, ⟨3847,
      by norm_num⟩, ⟨3851, by norm_num⟩, ⟨3853, by norm_num⟩, ⟨3863, by norm_num⟩,
      ⟨3877, by norm_num⟩, ⟨3881, by norm_num⟩, ⟨3889, by norm_num⟩, ⟨3907, by
      norm_num⟩, ⟨3911, by norm_num⟩, ⟨3917, by norm_num⟩, ⟨3919, by norm_num⟩, ⟨3923,
      by norm_num⟩, ⟨3929, by norm_num⟩, ⟨3931, by norm_num⟩, ⟨3943, by norm_num⟩,
      ⟨3947, by norm_num⟩, ⟨3967, by norm_num⟩, ⟨3989, by norm_num⟩, ⟨4001, by
      norm_num⟩, ⟨4003, by norm_num⟩, ⟨4007, by norm_num⟩, ⟨4013, by norm_num⟩, ⟨4019,
      by norm_num⟩, ⟨4021, by norm_num⟩, ⟨4027, by norm_num⟩, ⟨4049, by norm_num⟩,
      ⟨4051, by norm_num⟩, ⟨4057, by norm_num⟩, ⟨4073, by norm_num⟩, ⟨4079, by
      norm_num⟩, ⟨4091, by norm_num⟩, ⟨4093, by norm_num⟩, ⟨4099, by norm_num⟩, ⟨4111,
      by norm_num⟩, ⟨4127, by norm_num⟩, ⟨4129, by norm_num⟩, ⟨4133, by norm_num⟩,
      ⟨4139, by norm_num⟩, ⟨4153, by norm_num⟩, ⟨4157, by norm_num⟩, ⟨4159, by
      norm_num⟩, ⟨4177, by norm_num⟩, ⟨4201, by norm_num⟩, ⟨4211, by norm_num⟩, ⟨4217,
      by norm_num⟩, ⟨4219, by norm_num⟩, ⟨4229, by norm_num⟩, ⟨4231, by norm_num⟩,
      ⟨4241, by norm_num⟩, ⟨4243, by norm_num⟩, ⟨4253, by norm_num⟩, ⟨4259, by
      norm_num⟩, ⟨4261, by norm_num⟩, ⟨4271, by norm_num⟩, ⟨4273, by norm_num⟩, ⟨4283,
      by norm_num⟩, ⟨4289, by norm_num⟩, ⟨4297, by norm_num⟩, ⟨4327, by norm_num⟩,
      ⟨4337, by norm_num⟩, ⟨4339, by norm_num⟩, ⟨4349, by norm_num⟩, ⟨4357, by
      norm_num⟩, ⟨4363, by norm_num⟩, ⟨4373, by norm_num⟩, ⟨4391, by norm_num⟩, ⟨4397,
      by norm_num⟩, ⟨4409, by norm_num⟩, ⟨4421, by norm_num⟩, ⟨4423, by norm_num⟩,
      ⟨4441, by norm_num⟩, ⟨4447, by norm_num⟩, ⟨4451, by norm_num⟩, ⟨4457, by
      norm_num⟩, ⟨4463, by norm_num⟩, ⟨4481, by norm_num⟩, ⟨4483, by norm_num⟩, ⟨4493,
      by norm_num⟩, ⟨4507, by norm_num⟩, ⟨4513, by norm_num⟩, ⟨4517, by norm_num⟩,
      ⟨4519, by norm_num⟩, ⟨4523, by norm_num⟩, ⟨4547, by norm_num⟩, ⟨4549, by
      norm_num⟩, ⟨4561, by norm_num⟩, ⟨4567, by norm_num⟩, ⟨4583, by norm_num⟩, ⟨4591,
      by norm_num⟩, ⟨4597, by norm_num⟩, ⟨4603, by norm_num⟩, ⟨4621, by norm_num⟩,
      ⟨4637, by norm_num⟩, ⟨4639, by norm_num⟩, ⟨4643, by norm_num⟩, ⟨4649, by
      norm_num⟩, ⟨4651, by norm_num⟩, ⟨4657, by norm_num⟩, ⟨4663, by norm_num⟩, ⟨4673,
      by norm_num⟩, ⟨4679, by norm_num⟩, ⟨4691, by norm_num⟩, ⟨4703, by norm_num⟩,
      ⟨4721, by norm_num⟩, ⟨4723, by norm_num⟩, ⟨4729, by norm_num⟩, ⟨4733, by
      norm_num⟩, ⟨4751, by norm_num⟩, ⟨4759, by norm_num⟩, ⟨4783, by norm_num⟩, ⟨4787,
      by norm_num⟩, ⟨4789, by norm_num⟩, ⟨4793, by norm_num⟩, ⟨4799, by norm_num⟩,
      ⟨4801, by norm_num⟩, ⟨4813, by norm_num⟩, ⟨4817, by norm_num⟩, ⟨4831, by
      norm_num⟩, ⟨4861, by norm_num⟩, ⟨4871, by norm_num⟩, ⟨4877, by norm_num⟩, ⟨4889,
      by norm_num⟩, ⟨4903, by norm_num⟩, ⟨4909, by norm_num⟩, ⟨4919, by norm_num⟩,
      ⟨4931, by norm_num⟩, ⟨4933, by norm_num⟩, ⟨4937, by norm_num⟩, ⟨4943, by
      norm_num⟩, ⟨4951, by norm_num⟩, ⟨4957, by norm_num⟩, ⟨4967, by norm_num⟩, ⟨4969,
      by norm_num⟩, ⟨4973, by norm_num⟩, ⟨4987, by norm_num⟩, ⟨4993, by norm_num⟩,
      ⟨4999, by norm_num⟩
  }

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000000 in
/-- The sharper lower bound on `d` that the odd side needs.

`betaOdd = d(log 2 - Sodd + γ) ≥ 0.1556` requires `d ≥ 0.378682252653`, against
the `0.3785631789` the unrestricted side needs, so `dConst_lower_bound`'s 94
primes fall short and this takes 668.

Note `0.3786823`, not `0.3786822`: truncating the requirement to seven decimals
gives `0.3786822 * 0.4108985803 = 0.1555999784`, which is BELOW the `0.1556`
the step needs.  A sufficient bound must round UP.

The evaluation needs an enlarged `simp` step budget, not just recursion depth:
a `Finset` literal dedups pairwise, so 668 elements cost on the order of
223,000 membership rewrites against a default of 100,000. -/
theorem dConst_lower_bound_sharp : (0.3786823 : ℝ) ≤ dConst := by
  have hsub : dConst = (1 / 4) * ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 := by
    unfold dConst
    rw [dConst_prod_eq_subtype]
  have hone : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 : ℝ) ≤ (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 :=
    fun p => dConst_factor_one_le (p : ℕ) p.2.2
  have hpart := prod_le_hasProd_of_one_le dLowerSetSharp
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)
    _ hone dConst_family_multipliable.hasProd
  have heval : (∏ p ∈ dLowerSetSharp,
      (1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2)
      ≥ (4 * 0.3786823 : ℝ) := by
    norm_num (config := { maxSteps := 100000000, maxDischargeDepth := 4 })
      [dLowerSetSharp, Finset.prod_insert, Finset.mem_insert,
       Finset.mem_singleton, Subtype.mk.injEq]
  rw [hsub]
  linarith [hpart, heval]

/-- The `if 5 ≤ p` in rhoConst is the indicator of {p ≥ 5}.  Mirrors
`dConst_if_eq_indicator`, and is simpler because the guard is already the
threshold rather than `2 < p`. -/
theorem rhoConst_if_eq_indicator :
    (fun p : Nat.Primes =>
        (if 5 ≤ (p : ℕ) then (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 else 1))
      = Set.mulIndicator {p : Nat.Primes | (5 : ℕ) ≤ (p : ℕ)}
          (fun p : Nat.Primes => (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3) := by
  funext p
  by_cases h : p ∈ {q : Nat.Primes | (5 : ℕ) ≤ (q : ℕ)}
  · have h5 : (5 : ℕ) ≤ (p : ℕ) := h
    rw [Set.mulIndicator_of_mem h, if_pos h5]
  · have h5 : ¬((5 : ℕ) ≤ (p : ℕ)) := h
    rw [Set.mulIndicator_of_notMem h, if_neg h5]

/-- rhoConst's indicator product over all primes equals the p ≥ 5 subtype
product.  Mirrors `dConst_prod_eq_subtype`. -/
theorem rhoConst_prod_eq_subtype :
    (∏' p : Nat.Primes,
        (if 5 ≤ (p : ℕ) then (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 else 1))
      = ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
          (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 := by
  rw [rhoConst_if_eq_indicator]
  rw [← tprod_subtype {p : Nat.Primes | (5 : ℕ) ≤ (p : ℕ)}
    (fun p : Nat.Primes => (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3)]
  exact (primesEquivSubtypeGE 5).tprod_eq
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3)

/-- The rhoConst Euler factor, in closed form:

    (1 - 3/p)⁻¹ (1 - 1/p)³ = (p-1)³/(p²(p-3)) = 1 + (3p-1)/(p²(p-3)).

Rational in `p`, exactly as `dConst_factor_sub_one`, since
(p-1)³ - p²(p-3) = 3p - 1. -/
theorem rhoConst_factor_sub_one (p : ℕ) (hp : 5 ≤ p) :
    (1 - 3 / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) ^ 3 - 1
      = (3 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * ((p : ℝ) - 3)) := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp3 : (0 : ℝ) < (p : ℝ) - 3 := by linarith
  have hne : (1 : ℝ) - 3 / (p : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hcon
    field_simp at hcon
    linarith
  field_simp
  ring

/-- Every rhoConst factor is at least 1, since (3p-1)/(p²(p-3)) > 0 for p ≥ 5. -/
theorem rhoConst_factor_one_le (p : ℕ) (hp : 5 ≤ p) :
    (1 : ℝ) ≤ (1 - 3 / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) ^ 3 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) ^ 2 * ((p : ℝ) - 3) := by nlinarith
  have hnum : (0 : ℝ) < 3 * (p : ℝ) - 1 := by linarith
  have hpos : (0 : ℝ) < (3 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * ((p : ℝ) - 3)) :=
    div_pos hnum hden
  have := rhoConst_factor_sub_one p hp
  linarith

/-- The rhoConst family is multipliable over p ≥ 5.  Mirrors
`dConst_family_multipliable`; the comparison constant is 7 rather than 3
because (3p-1)/(p-3) is largest at p = 5, where it equals 7. -/
theorem rhoConst_family_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      7 * (1 / ((p : ℕ) : ℝ) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
      simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    exact (hbase.subtype _).mul_left 7
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 - 1) := by
    apply Summable.of_nonneg_of_le _ _ hcomp
    · intro p
      rw [rhoConst_factor_sub_one (p : ℕ) p.2.2]
      have hp5 : (5 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
      have hden : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) - 3) := by nlinarith
      have hnum : (0 : ℝ) < 3 * ((p : ℕ) : ℝ) - 1 := by linarith
      exact le_of_lt (div_pos hnum hden)
    · intro p
      rw [rhoConst_factor_sub_one (p : ℕ) p.2.2]
      have hp5 : (5 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.2
      have hden : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) - 3) := by nlinarith
      have hsq : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by positivity
      rw [show (7 : ℝ) * (1 / ((p : ℕ) : ℝ) ^ 2) = 7 / ((p : ℕ) : ℝ) ^ 2 by ring]
      rw [div_le_div_iff₀ hden hsq]
      nlinarith
  have h := Real.multipliable_one_add_of_summable hsum
  apply h.congr
  intro p
  ring

set_option maxRecDepth 1000000 in
/-- The 93 primes 5 ≤ p ≤ 499. -/
def rhoLowerSet : Finset {p : ℕ // p.Prime ∧ 5 ≤ p} :=
  {
      ⟨5, by norm_num⟩, ⟨7, by norm_num⟩, ⟨11, by norm_num⟩, ⟨13, by norm_num⟩, ⟨17,
      by norm_num⟩, ⟨19, by norm_num⟩, ⟨23, by norm_num⟩, ⟨29, by norm_num⟩, ⟨31, by
      norm_num⟩, ⟨37, by norm_num⟩, ⟨41, by norm_num⟩, ⟨43, by norm_num⟩, ⟨47, by
      norm_num⟩, ⟨53, by norm_num⟩, ⟨59, by norm_num⟩, ⟨61, by norm_num⟩, ⟨67, by
      norm_num⟩, ⟨71, by norm_num⟩, ⟨73, by norm_num⟩, ⟨79, by norm_num⟩, ⟨83, by
      norm_num⟩, ⟨89, by norm_num⟩, ⟨97, by norm_num⟩, ⟨101, by norm_num⟩, ⟨103, by
      norm_num⟩, ⟨107, by norm_num⟩, ⟨109, by norm_num⟩, ⟨113, by norm_num⟩, ⟨127, by
      norm_num⟩, ⟨131, by norm_num⟩, ⟨137, by norm_num⟩, ⟨139, by norm_num⟩, ⟨149, by
      norm_num⟩, ⟨151, by norm_num⟩, ⟨157, by norm_num⟩, ⟨163, by norm_num⟩, ⟨167, by
      norm_num⟩, ⟨173, by norm_num⟩, ⟨179, by norm_num⟩, ⟨181, by norm_num⟩, ⟨191, by
      norm_num⟩, ⟨193, by norm_num⟩, ⟨197, by norm_num⟩, ⟨199, by norm_num⟩, ⟨211, by
      norm_num⟩, ⟨223, by norm_num⟩, ⟨227, by norm_num⟩, ⟨229, by norm_num⟩, ⟨233, by
      norm_num⟩, ⟨239, by norm_num⟩, ⟨241, by norm_num⟩, ⟨251, by norm_num⟩, ⟨257, by
      norm_num⟩, ⟨263, by norm_num⟩, ⟨269, by norm_num⟩, ⟨271, by norm_num⟩, ⟨277, by
      norm_num⟩, ⟨281, by norm_num⟩, ⟨283, by norm_num⟩, ⟨293, by norm_num⟩, ⟨307, by
      norm_num⟩, ⟨311, by norm_num⟩, ⟨313, by norm_num⟩, ⟨317, by norm_num⟩, ⟨331, by
      norm_num⟩, ⟨337, by norm_num⟩, ⟨347, by norm_num⟩, ⟨349, by norm_num⟩, ⟨353, by
      norm_num⟩, ⟨359, by norm_num⟩, ⟨367, by norm_num⟩, ⟨373, by norm_num⟩, ⟨379, by
      norm_num⟩, ⟨383, by norm_num⟩, ⟨389, by norm_num⟩, ⟨397, by norm_num⟩, ⟨401, by
      norm_num⟩, ⟨409, by norm_num⟩, ⟨419, by norm_num⟩, ⟨421, by norm_num⟩, ⟨431, by
      norm_num⟩, ⟨433, by norm_num⟩, ⟨439, by norm_num⟩, ⟨443, by norm_num⟩, ⟨449, by
      norm_num⟩, ⟨457, by norm_num⟩, ⟨461, by norm_num⟩, ⟨463, by norm_num⟩, ⟨467, by
      norm_num⟩, ⟨479, by norm_num⟩, ⟨487, by norm_num⟩, ⟨491, by norm_num⟩, ⟨499, by
      norm_num⟩
  }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
/-- **A certified bound on `rho`, proved rather than assumed.**

`rhoConst = -(1/9) ∏'_{p ≥ 5} (1 - 3/p)⁻¹(1 - 1/p)³`, every factor of which
exceeds 1 by `rhoConst_factor_one_le`.  The product over a finite set is
therefore a lower bound for the whole product -- and because the `-(1/9)`
makes rhoConst NEGATIVE, that becomes an UPPER bound on rhoConst.

Which direction is reachable matters elsewhere; here it does not, because
`rho_enclosure` has no consumer anywhere in the development -- `grep` for it
returns the field declarations and a comment, nothing more.  So any true
bound discharges it, and the field can go.

The 93 primes p ≤ 499 give `rhoConst ≤ -0.174788567...`; the certified value
is `-0.1749323`.  Note that for an upper bound on a NEGATIVE quantity the
numeral must be rounded TOWARD ZERO to stay valid, which is the opposite of
the `d` case. -/
theorem rhoConst_upper_bound : rhoConst ≤ (-0.1747885 : ℝ) := by
  have hsub : rhoConst = -(1 / 9) * ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 := by
    unfold rhoConst
    rw [rhoConst_prod_eq_subtype]
  have hone : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 : ℝ) ≤ (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3 :=
    fun p => rhoConst_factor_one_le (p : ℕ) p.2.2
  have hpart := prod_le_hasProd_of_one_le rhoLowerSet
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3)
    _ hone rhoConst_family_multipliable.hasProd
  have heval : (∏ p ∈ rhoLowerSet,
      (1 - 3 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 3)
      ≥ (-9 * -0.1747885 : ℝ) := by
    norm_num (config := { maxSteps := 100000000, maxDischargeDepth := 4 })
      [rhoLowerSet, Finset.prod_insert, Finset.mem_insert,
       Finset.mem_singleton, Subtype.mk.injEq]
  rw [hsub]
  linarith [hpart, heval]

/-- The certified inputs: everything the analytic reduction takes on trust.

Each field is an Arb ball computation from the companion package, exactly the
division Section 8 draws.  The analytic reduction is machine-verified;
these are not.

Umax and Vmax are parameters rather than fields because a Prop cannot carry
data; the manuscript's values are 0.08436 and 1.90747, valid for k >= 900. -/
structure NumericalFacts (Sstar alph Gam Umax Vmax : ℝ) : Prop where
  /-- Section 3.4: S* <= 6.9764.  This read 6.9763 until the certified sum was
  recomputed: it is 6.97633273, and the head i <= 30 alone is 6.97633205, so
  6.9763 was not an upper bound -- 6.97633 rounded down where an upper bound
  must round up.  Nothing downstream moves, because the numerics compute S*
  internally (k1_far_range.py) and never read the stated value.  But the
  hypothesis was unsatisfiable by the real S*, which made the theorems
  assuming it vacuous at the point of use. -/
  Sstar_bound   : Sstar ≤ 6.9764
  /-- Section 3.5: alpha_+ from the 1600-box beta_i sweep. -/
  alpha_bound   : alph ≤ 15.4257
  /-- Theorem 6.1: Gamma from the 800-box gammahat_i sweep.

  **This field has no consumer.**  `Gam` occurs nowhere in this development
  except the structure signatures, the theorem signatures, and this line: no
  other field mentions it, and neither `erdos_sums_increase_from_six` nor
  `erdos_sums_increase_from_six'` uses it.  So it constrains a bound variable
  that nothing reads, and nothing the theorems prove rests on it.

  It is kept rather than deleted because CLAUDE.md requires every certified
  constant to appear in all three places, and `Gam` has no defined counterpart
  here to prove something about -- unlike `rho`, whose field could be replaced
  by the proved `rhoConst_upper_bound`.  Deleting this would leave the
  manuscript's Theorem 6.1 constant with no Lean mirror at all, which is worse
  drift than a vacuous mirror.

  Two consequences worth stating plainly.  The trusted base is SMALLER than
  the field count suggests -- this field, `MR_bound`, and the bounds and
  nonnegativity facts on abstract variables assert nothing about the world.
  And if the reduction is ever rerouted through Theorem 6.1, this field
  becomes load-bearing without anything here changing, so the note belongs
  next to the field rather than only in TRUSTED-BASE.md. -/
  Gamma_bound   : Gam ≤ 104.52
  /-- Section 7: the aggregate source bound for k >= 2440. -/
  source_bound  : ∀ k : ℕ, 2440 ≤ k →
    |2 * E aOneConst k - E aOneConst (k + 1)|
      ≤ RBound Umax Vmax Sstar alph k
  /-- `phi_mono` stood here.  It is now proved -- `phiBound_mono_of_bounds` --
  and what it needed that this structure did not carry is an upper bound on
  `Umax`, which the manuscript states as `|U| <= 0.08436`.  The three
  nonnegativity fields are free in any instantiation: all of these parameters
  are bounds on absolute values.  A universally quantified assumption about a
  quadratic, which no finite computation can discharge and no reader can check
  by inspection, is replaced by scalars `verify.py` can check. -/
  Umax_nonneg   : 0 ≤ Umax
  U_bound       : Umax ≤ 0.08436
  Vmax_nonneg   : 0 ≤ Vmax
  V_bound       : Vmax ≤ 1.90747
  Sstar_nonneg  : 0 ≤ Sstar
  alph_nonneg   : 0 ≤ alph
  /-- Theorem 1.1, the prior certified f_k computation: 6 <= k <= 199. -/
  sweep_low     : ∀ k : ℕ, 6 ≤ k → k ≤ 199 → f k < f (k + 1)
  /-- Theorem 6.2, the refined criterion sweep: 78 <= k <= 899. -/
  sweep_mid     : ∀ k : ℕ, 78 ≤ k → k ≤ 899 → f k < f (k + 1)
  /-- Section 5, the extended delta-table sweep: 900 <= k <= 2439. -/
  sweep_high    : ∀ k : ℕ, 900 ≤ k → k ≤ 2439 → f k < f (k + 1)

/-- The T_k tail bound denominator is positive for k ≥ 1. -/
lemma Tk_bound_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < (k : ℝ) * Real.log 2 * (2 ^ k - 1) := by
  have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
    have : (1 : ℝ) < 2 ^ k := by
      calc (1 : ℝ) < 2 ^ 1 := by norm_num
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
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
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
        ring

/-- Σ_{i=0}^{m} (2u)^i/i! ≤ exp(2u) for u ≥ 0. -/
lemma sum_exp_terms_le (u : ℝ) (hu : 0 ≤ u) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (2 * u) ^ i / Nat.factorial i ≤ Real.exp (2 * u) := by
  have h2u : (0 : ℝ) ≤ 2 * u := by linarith
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummable : Summable (fun i => (2 * u) ^ i / Nat.factorial i) :=
    Real.summable_pow_div_factorial (2 * u)
  have hnn : ∀ i ∉ Finset.range (m + 1), (0 : ℝ) ≤ (2 * u) ^ i / Nat.factorial i := by
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
    ∫ s in Set.Ioi (1 : ℝ), (n : ℝ) ^ (-s) =
      1 / ((n : ℝ) * Real.log n) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hpteq : ∀ s : ℝ, (n : ℝ) ^ (-s) = Real.exp (-(Real.log n * s)) := by
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
    f k = ∫ s in Set.Ioi (1 : ℝ), Fk k s := by
  unfold f Fk
  have habs : ∀ (n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k}) (s : ℝ),
      ‖(n : ℝ) ^ (-s)‖ = (n : ℝ) ^ (-s) := by
    intro n s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm_eq : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      ∫ s in Set.Ioi (1 : ℝ), ‖(n : ℝ) ^ (-s)‖ = 1 / ((n : ℝ) * Real.log n) := by
    intro n
    simp_rw [habs]
    exact integral_n_neg_s n n.2.1
  have hsummable_norm : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      ∫ s in Set.Ioi (1 : ℝ), ‖(n : ℝ) ^ (-s)‖) := by
    simp_rw [hnorm_eq]; exact hsum1
  have hint : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      MeasureTheory.Integrable (fun s => (n : ℝ) ^ (-s))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    intro n
    by_contra hni
    have hz := MeasureTheory.integral_undef hni
    rw [integral_n_neg_s n n.2.1] at hz
    have : (0 : ℝ) < 1 / ((n : ℝ) * Real.log n) := by
      have hn2 : 2 ≤ (n : ℕ) := n.2.1
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < (n : ℕ))
      have := Real.log_pos this
      positivity
    linarith [hz ▸ this]
  rw [tsum_congr (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} => (integral_n_neg_s n n.2.1).symm)]
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable_norm

/-- The function s ↦ n^{-s} is continuous. -/
lemma continuous_n_neg_s (n : ℕ) (hn : 2 ≤ n) : Continuous (fun s : ℝ => (n : ℝ) ^ (-s)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  exact (Real.continuous_const_rpow hnpos.ne').comp continuous_neg

/-- n^{-s} is integrable on Ioi 1. -/
lemma integrable_n_neg_s_Ioi1 (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.Integrable (fun s : ℝ => (n : ℝ) ^ (-s))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
  by_contra hni
  have hz := MeasureTheory.integral_undef hni
  rw [integral_n_neg_s n hn] at hz
  have : (0 : ℝ) < 1 / ((n : ℝ) * Real.log n) := by
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have := Real.log_pos hn1
    positivity
  linarith [hz ▸ this]

/-- n^{-s} is integrable on Ioi 2 (via Ioi 2 ⊆ Ioi 1). -/
lemma integrable_n_neg_s_Ioi2 (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.Integrable (fun s : ℝ => (n : ℝ) ^ (-s))
      (MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ))) := by
  have hsub : Set.Ioi (2 : ℝ) ⊆ Set.Ioi (1 : ℝ) := fun x hx => lt_trans (by norm_num : (1 : ℝ) < 2) hx
  exact MeasureTheory.IntegrableOn.mono_set (integrable_n_neg_s_Ioi1 n hn) hsub

/-- Splitting the improper integral at s=2. -/
lemma integral_n_neg_s_split (n : ℕ) (hn : 2 ≤ n) :
    ∫ s in Set.Ioi (1 : ℝ), (n : ℝ) ^ (-s) ∂MeasureTheory.volume =
      ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume +
        ∫ s in Set.Ioi (2 : ℝ), (n : ℝ) ^ (-s) ∂MeasureTheory.volume := by
  have hunion : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) 2 ∪ Set.Ioi (2 : ℝ) := by
    rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)]
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) 2) (Set.Ioi (2 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx2⟩ hx2'
    exact absurd hx2 (not_le.mpr hx2')
  rw [hunion]
  exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    ((continuous_n_neg_s n hn).integrableOn_Ioc)
    (integrable_n_neg_s_Ioi2 n hn)

/-- ∫₂^∞ n^{-s} ds = 1/(n² log n) for n ≥ 2. -/
lemma integral_n_neg_s_Ioi2_value (n : ℕ) (hn : 2 ≤ n) :
    ∫ s in Set.Ioi (2 : ℝ), (n : ℝ) ^ (-s) ∂MeasureTheory.volume =
      1 / ((n : ℝ) ^ 2 * Real.log n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hpteq : ∀ s : ℝ, (n : ℝ) ^ (-s) = Real.exp (-(Real.log n * s)) := by
    intro s
    rw [Real.rpow_def_of_pos hnpos]
    congr 1; ring
  simp_rw [hpteq]
  rw [MeasureTheory.integral_comp_mul_left_Ioi (fun u => Real.exp (-u)) 2 hlogn]
  simp only [smul_eq_mul]
  rw [integral_exp_neg_Ioi, Real.exp_neg]
  have hexp2 : Real.exp (Real.log n * 2) = (n : ℝ) ^ 2 := by
    have heq : Real.log (n : ℝ) * 2 = Real.log n + Real.log n := by ring
    rw [heq, Real.exp_add, Real.exp_log hnpos]
    ring
  rw [hexp2]
  rw [one_div, mul_inv]
  ring

/-- I_k := ∫₁² F_k(s) ds. -/
noncomputable def Ik (k : ℕ) : ℝ := ∫ s in Set.Ioc (1 : ℝ) 2, Fk k s ∂MeasureTheory.volume

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
      0 ≤ ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume ∧
      ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume
        ≤ 1 / ((n : ℝ) * Real.log n) := by
    intro n
    have hsplit := integral_n_neg_s_split n (hn2 n)
    have hpt := integral_n_neg_s n (hn2 n)
    have hIoi2nonneg : 0 ≤ ∫ s in Set.Ioi (2 : ℝ), (n : ℝ) ^ (-s) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_nonneg; intro s; positivity
    have hIocnonneg : 0 ≤ ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_nonneg; intro s; positivity
    refine ⟨hIocnonneg, ?_⟩
    rw [← hpt]
    linarith [hsplit, hIoi2nonneg]
  have hsummable_Ioc : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume) :=
    Summable.of_nonneg_of_le (fun n => (hIoc_le n).1) (fun n => (hIoc_le n).2) hsum1
  have hTk_le : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      0 ≤ 1 / ((n : ℝ) ^ 2 * Real.log n) ∧
        1 / ((n : ℝ) ^ 2 * Real.log n) ≤ 1 / ((n : ℝ) * Real.log n) := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) (hn2 n))
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < (n : ℕ))
    have hlogn := Real.log_pos hn1
    have hnpos2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnpos 2
    have hprod : 0 < (n : ℝ) ^ 2 * Real.log n := mul_pos hnpos2 hlogn
    have hprod1 : 0 < (n : ℝ) * Real.log n := mul_pos hnpos hlogn
    constructor
    · exact le_of_lt (div_pos (by norm_num) hprod)
    · apply div_le_div_of_nonneg_left (by norm_num) hprod1
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hsummable_Tk : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
      1 / ((n : ℝ) ^ 2 * Real.log n)) :=
    Summable.of_nonneg_of_le (fun n => (hTk_le n).1) (fun n => (hTk_le n).2) hsum1
  unfold f
  rw [tsum_congr (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
    (integral_n_neg_s n (hn2 n)).symm)]
  have hpt_split2 : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
      ∫ s in Set.Ioi (1 : ℝ), (n : ℝ) ^ (-s) ∂MeasureTheory.volume =
        ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume +
          1 / ((n : ℝ) ^ 2 * Real.log n) := by
    intro n
    rw [integral_n_neg_s_split n (hn2 n), integral_n_neg_s_Ioi2_value n (hn2 n)]
  rw [tsum_congr hpt_split2, Summable.tsum_add hsummable_Ioc hsummable_Tk]
  congr 1
  · have hint : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
        MeasureTheory.Integrable (fun s : ℝ => (n : ℝ) ^ (-s))
          (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2)) :=
      fun n => (continuous_n_neg_s n (hn2 n)).integrableOn_Ioc
    unfold Ik Fk
    have hnorm_eq : ∀ n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k},
        ∫ s in Set.Ioc (1 : ℝ) 2, ‖(n : ℝ) ^ (-s)‖ ∂MeasureTheory.volume =
          ∫ s in Set.Ioc (1 : ℝ) 2, (n : ℝ) ^ (-s) ∂MeasureTheory.volume := by
      intro n
      congr 1
      funext s
      exact Real.norm_of_nonneg (by positivity)
    have hsummable_norm2 : Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} =>
        ∫ s in Set.Ioc (1 : ℝ) 2, ‖(n : ℝ) ^ (-s)‖ ∂MeasureTheory.volume) :=
      hsummable_Ioc.congr (fun n => (hnorm_eq n).symm)
    exact MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable_norm2

/-- LINK 3 (assembly), pure algebra given the coefficient sums as data. -/
theorem assembly_identity (k : ℕ) (c δ : ℕ → ℝ) (q : ℝ) :
    ∑ i ∈ Finset.range (k + 1), c i * 2 ^ i * (2 ^ (k - i + 1) - q * ((k - i : ℕ):ℝ) ^ 2 + δ (k - i)) =
      2 ^ (k + 1) * (∑ i ∈ Finset.range (k + 1), c i) -
        q * ((k : ℝ) ^ 2 * (∑ i ∈ Finset.range (k + 1), 2 ^ i * c i) -
          2 * k * (∑ i ∈ Finset.range (k + 1), (i : ℝ) * 2 ^ i * c i) +
          (∑ i ∈ Finset.range (k + 1), (i : ℝ) ^ 2 * 2 ^ i * c i)) +
        (∑ i ∈ Finset.range (k + 1), 2 ^ i * c i * δ (k - i)) := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      c i * 2 ^ i * (2 ^ (k - i + 1) - q * ((k - i : ℕ):ℝ) ^ 2 + δ (k - i)) =
        c i * 2 ^ (k + 1) -
          q * (c i * 2 ^ i * (k : ℝ) ^ 2 - 2 * k * (c i * 2 ^ i * (i : ℝ)) + c i * 2 ^ i * (i : ℝ) ^ 2) +
          c i * 2 ^ i * δ (k - i) := by
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi; omega
    have hcast : ((k - i : ℕ):ℝ) = (k : ℝ) - (i : ℝ) := Nat.cast_sub hik
    have hexp : (2 : ℝ) ^ i * 2 ^ (k - i + 1) = 2 ^ (k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hcast]
    have expand :
        c i * 2 ^ i * ((2 : ℝ) ^ (k - i + 1) - q * ((k : ℝ) - i) ^ 2 + δ (k - i)) =
          c i * (2 ^ i * 2 ^ (k - i + 1)) -
            q * (c i * 2 ^ i * ((k : ℝ) - i) ^ 2) + c i * 2 ^ i * δ (k - i) := by
      ring
    rw [expand, hexp]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
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
  have hderiv : ∀ y ∈ Set.Ico (0 : ℝ) 1, HasDerivAt (fun t => Real.log (1 - t) + t)
      (-1 / (1 - y) + 1) y := by
    intro y hy
    have hy1 : (1 : ℝ) - y ≠ 0 := by
      have := hy.2; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - y)) y := by
      have := h1.log hy1
      simpa using this
    exact h2.add (hasDerivAt_id y)
  have hanti : AntitoneOn (fun t => Real.log (1 - t) + t) (Set.Ico (0 : ℝ) 1) := by
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
      have hy1 : (0 : ℝ) < 1 - y := by linarith [hy.2]
      have hyy : (0 : ℝ) ≤ y := hy.1.le
      have heq : -1 / (1 - y) + 1 = -y / (1 - y) := by field_simp; ring
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hy1.le
  have h0 := hanti (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) (Set.mem_Ico.mpr ⟨hx0, hx1⟩) hx0
  simpa using h0

/-- log(1-x)+x ≥ -x²/(1-x) for x ∈ [0,1). -/
theorem log_one_sub_add_self_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -(x^2 / (1 - x)) ≤ Real.log (1 - x) + x := by
  have hderiv : ∀ y ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt (fun t => Real.log (1 - t) + t + t^2 / (1 - t))
        (-1 / (1 - y) + 1 + (2 * y * (1 - y) - y^2 * (-1)) / (1 - y)^2) y := by
    intro y hy
    have hy1 : (1 : ℝ) - y ≠ 0 := by
      have := hy.2; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - y)) y := by
      have := h1.log hy1
      simpa using this
    have h3 : HasDerivAt (fun t : ℝ => t^2) (2 * y) y := by
      have := hasDerivAt_pow 2 y
      simpa using this
    have h4 : HasDerivAt (fun t : ℝ => t^2 / (1 - t))
        ((2 * y * (1 - y) - y^2 * (-1)) / (1 - y)^2) y := h3.div h1 hy1
    exact (h2.add (hasDerivAt_id y)).add h4
  have hmono : MonotoneOn (fun t => Real.log (1 - t) + t + t^2 / (1 - t)) (Set.Ico (0 : ℝ) 1) := by
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
      have hy1 : (0 : ℝ) < 1 - y := by linarith [hy.2]
      have hyy : (0 : ℝ) ≤ y := hy.1.le
      have heq : -1 / (1 - y) + 1 + (2 * y * (1 - y) - y^2 * (-1)) / (1 - y)^2 = y / (1 - y)^2 := by
        field_simp; ring
      rw [heq]
      positivity
  have h0 := hmono (Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩) (Set.mem_Ico.mpr ⟨hx0, hx1⟩) hx0
  simp only [Real.log_one, sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_div, add_zero] at h0
  linarith

/-- log(1+y)-y ≤ 0 for y ≥ 0. -/
theorem log_one_add_sub_self_nonpos (y : ℝ) (hy0 : 0 ≤ y) :
    Real.log (1 + y) - y ≤ 0 := by
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt (fun s => Real.log (1 + s) + -s)
      (1 / (1 + t) + -1) t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have ht1 : (1 : ℝ) + t ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      have := h1.log ht1
      simpa using this
    have h3 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    exact h2.add h3
  have hanti : AntitoneOn (fun s => Real.log (1 + s) + -s) (Set.Ici (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · apply ContinuousOn.add
      · apply ContinuousOn.log (by fun_prop)
        intro t ht
        have ht0 : (0 : ℝ) ≤ t := ht
        positivity
      · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hderiv t (Set.mem_Ici.mpr ht.le)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0 : ℝ) < t := ht
      have hd := hderiv t (Set.mem_Ici.mpr ht0.le)
      rw [hd.deriv]
      have ht1 : (0 : ℝ) < 1 + t := by linarith
      have : (1 : ℝ) / (1 + t) ≤ 1 := by
        rw [div_le_one ht1]; linarith
      linarith
  have h0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy0) hy0
  simp only [Real.log_one, add_zero] at h0
  linarith

/-- log(1+y)-y ≥ -y²/2 for y ≥ 0. -/
theorem log_one_add_sub_self_lower (y : ℝ) (hy0 : 0 ≤ y) :
    -(y^2 / 2) ≤ Real.log (1 + y) - y := by
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s => Real.log (1 + s) + -s + s^2 / 2)
        (1 / (1 + t) + -1 + t) t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have ht1 : (1 : ℝ) + t ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      have := h1.log ht1
      simpa using this
    have h3neg : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    have h4 : HasDerivAt (fun s : ℝ => s^2 / 2) t t := by
      have := (hasDerivAt_pow 2 t).div_const 2
      simpa using this
    exact (h2.add h3neg).add h4
  have hmono : MonotoneOn (fun s => Real.log (1 + s) + -s + s^2 / 2) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · apply ContinuousOn.add
      · apply ContinuousOn.add
        · apply ContinuousOn.log (by fun_prop)
          intro t ht
          have ht0 : (0 : ℝ) ≤ t := ht
          positivity
        · fun_prop
      · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hderiv t (Set.mem_Ici.mpr ht.le)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0 : ℝ) < t := ht
      have hd := hderiv t (Set.mem_Ici.mpr ht0.le)
      rw [hd.deriv]
      have ht1 : (0 : ℝ) < 1 + t := by linarith
      have hkey : 1 / (1 + t) + -1 + t = t^2 / (1 + t) := by
        field_simp; ring
      rw [hkey]; positivity
  have h0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy0) hy0
  simp only [add_zero, Real.log_one] at h0
  linarith

/-- Combined two-sided log bound: |log(1-x)+x| ≤ 3x² for |x| ≤ 2 / 3. -/
theorem log_bound_combined (x : ℝ) (hx : |x| ≤ 2 / 3) :
    |Real.log (1 - x) + x| ≤ 3 * x^2 := by
  by_cases hx0 : (0 : ℝ) ≤ x
  · have hx1 : x < 1 := by
      have := abs_le.mp hx; linarith [this.2]
    have hub := log_one_sub_add_self_nonpos x hx0 hx1
    have hlb := log_one_sub_add_self_lower x hx0 hx1
    have hxle : x ≤ 2 / 3 := (abs_le.mp hx).2
    have h1mx : (1 : ℝ)/3 ≤ 1 - x := by linarith
    rw [abs_le]
    constructor
    · have : x^2 / (1 - x) ≤ 3 * x^2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - x)]
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

/-- Sharper variant of log_bound_combined on the smaller range |x| <= 1/5,
where 1 - x >= 4/5 gives the constant 5/4 in place of 3.
Needed for the wide-radius chain at |z| <= 29/10: the 5/2-radius proof has
enough slack at constant 3, but 29/10 does not. -/
theorem log_bound_combined_fifth (x : ℝ) (hx : |x| ≤ 1 / 5) :
    |Real.log (1 - x) + x| ≤ (5 / 4) * x^2 := by
  by_cases hx0 : (0 : ℝ) ≤ x
  · have hx1 : x < 1 := by
      have := abs_le.mp hx; linarith [this.2]
    have hub := log_one_sub_add_self_nonpos x hx0 hx1
    have hlb := log_one_sub_add_self_lower x hx0 hx1
    have hxle : x ≤ 1 / 5 := (abs_le.mp hx).2
    have h1mx : (4 : ℝ)/5 ≤ 1 - x := by linarith
    rw [abs_le]
    constructor
    · have : x^2 / (1 - x) ≤ (5 / 4) * x^2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - x)]
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
    |(-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))|
      ≤ 18 * (p : ℝ) ^ (-2*s) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hza_le : |z * a| ≤ 2 / 3 := by
    rw [abs_mul, abs_of_pos ha_pos]
    have hmm : |z| * a ≤ 2 * (1 / 3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have ha_le2 : |a| ≤ 2 / 3 := by rw [abs_of_pos ha_pos]; linarith
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
  have heq : (18 : ℝ) * a^2 = 18 * (p : ℝ) ^ (-2*s) := by
    rw [ha_def, ← Real.rpow_natCast ((p : ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
    ring_nf
  calc |(-(Real.log (1 - z * a) + z * a) + z * (Real.log (1 - a) + a))|
      ≤ |Real.log (1 - z * a) + z * a| + |z * (Real.log (1 - a) + a)| := hstep1
    _ ≤ 3 * (z*a)^2 + |z| * (3 * a^2) := hfinal
    _ ≤ 18 * a^2 := hbound
    _ = 18 * (p : ℝ) ^ (-2*s) := heq

/-- Summability of the per-prime correction terms. -/
theorem prime_correction_summable (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      |(-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))|) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => 18 * (p : ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (18 : ℝ) * (p : ℝ) ^ (-2*s) =
        18 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => abs_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => prime_correction_bound (p : ℕ) p.property.2 s hs z hz)
    hcomp

/-- |exp(x)-1| ≤ 2|x| for |x| ≤ 1. -/
theorem abs_exp_sub_one_le (x : ℝ) (hx : |x| ≤ 1) : |Real.exp x - 1| ≤ 2 * |x| := by
  by_cases hx0 : x ≤ 0
  · have hlb : (1 : ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hub : Real.exp x ≤ 1 := by
      have := Real.exp_le_exp.mpr hx0
      simpa using this
    rw [abs_of_nonpos (by linarith : Real.exp x - 1 ≤ 0)]
    rw [abs_of_nonpos hx0]
    linarith
  · push Not at hx0
    have hx1 : x ≤ 1 := by
      have := abs_le.mp hx; linarith [this.2]
    have hlog2mem : Real.log 2 ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨Real.log_nonneg (by norm_num), ?_⟩
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have he3 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hderiv : ∀ t : ℝ, HasDerivAt (fun u => 1 + 2*u + -Real.exp u) (2 + -Real.exp t) t := by
      intro t
      have h1 : HasDerivAt (fun u : ℝ => 1 + 2*u) 2 t := by
        simpa using ((hasDerivAt_id t).const_mul 2).const_add (1 : ℝ)
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
              rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
              exact Real.exp_le_exp.mpr ht.2.le
            linarith
        have h0 := hmono (Set.mem_Icc.mpr ⟨le_refl 0, hlog2mem.1⟩)
          (Set.mem_Icc.mpr ⟨hx0.le, hcase⟩) hx0.le
        simp only [mul_zero, add_zero, Real.exp_zero] at h0
        linarith
      · push Not at hcase
        have hmono : AntitoneOn (fun u => 1 + 2*u + -Real.exp u) (Set.Icc (Real.log 2) 1) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc (Real.log 2) 1)
          · fun_prop
          · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [interior_Icc] at ht
            rw [(hderiv t).deriv]
            have : (2 : ℝ) ≤ Real.exp t := by
              rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
              exact Real.exp_le_exp.mpr ht.1.le
            linarith
        have h0 := hmono (Set.mem_Icc.mpr ⟨hcase.le, hx1⟩)
          (Set.mem_Icc.mpr ⟨hlog2mem.2, le_refl 1⟩) hx1
        simp only at h0
        nlinarith [h0, he3]
    have hlb : (1 : ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp x - 1)]
    rw [abs_of_pos hx0]
    linarith

/-- For p ≥ 5, s ≥ 1: 18p^{-2s} ≤ 1. p=3 handled separately later
    as an ordinary finite factor, not through Multipliable machinery. -/
theorem correction_le_one (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    18 * (p : ℝ) ^ (-2*s) ≤ 1 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : (p : ℝ) ^ (-2*s) ≤ (p : ℝ) ^ (-2:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpow : (5 : ℝ) ^ (2 : ℝ) ≤ (p : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hp5 (by norm_num)
  have heq5 : (5 : ℝ) ^ (-2:ℝ) = ((5 : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) 2
  have heqp : (p : ℝ) ^ (-2:ℝ) = ((p : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg hpos.le 2
  have h2 : (p : ℝ) ^ (-2:ℝ) ≤ (5 : ℝ) ^ (-2:ℝ) := by
    rw [heqp, heq5]
    gcongr
  have h5val : (5 : ℝ) ^ (-2:ℝ) = 1 / 25 := by
    rw [heq5]
    norm_num [Real.rpow_natCast]
  have hchain : (p : ℝ) ^ (-2*s) ≤ 1 / 25 := le_trans h1 (h2.trans_eq h5val)
  linarith [hchain]

/-- Wide-radius variant: 20 p^(-2s) <= 1 for p >= 5 (20 / 25 = 0.8). -/
theorem correction_le_one_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    24 * (p : ℝ) ^ (-2*s) ≤ 1 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : (p : ℝ) ^ (-2*s) ≤ (p : ℝ) ^ (-2:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpow : (5 : ℝ) ^ (2 : ℝ) ≤ (p : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hp5 (by norm_num)
  have heq5 : (5 : ℝ) ^ (-2:ℝ) = ((5 : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) 2
  have heqp : (p : ℝ) ^ (-2:ℝ) = ((p : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg hpos.le 2
  have h2 : (p : ℝ) ^ (-2:ℝ) ≤ (5 : ℝ) ^ (-2:ℝ) := by
    rw [heqp, heq5]
    gcongr
  have h5val : (5 : ℝ) ^ (-2:ℝ) = 1 / 25 := by
    rw [heq5]
    norm_num [Real.rpow_natCast]
  have hchain : (p : ℝ) ^ (-2*s) ≤ 1 / 25 := le_trans h1 (h2.trans_eq h5val)
  linarith [hchain]

/-- |exp(correction_p) - 1| ≤ 36 p^{-2s} for p ≥ 5. -/
theorem prime_factor_sub_one_bound (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |Real.exp ((-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))) - 1|
      ≤ 36 * (p : ℝ) ^ (-2*s) := by
  set c : ℝ := (-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))
    with hc_def
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have : (5 : ℕ) ≤ p := hp
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast this
    linarith
  have hp3nat : 3 ≤ p := by omega
  have hbound : |c| ≤ 18 * (p : ℝ) ^ (-2*s) := prime_correction_bound p hp3nat s hs z hz
  have hle1 : 18 * (p : ℝ) ^ (-2*s) ≤ 1 := correction_le_one p hp s hs
  have hc1 : |c| ≤ 1 := le_trans hbound hle1
  have hexp := abs_exp_sub_one_le c hc1
  calc |Real.exp c - 1| ≤ 2 * |c| := hexp
    _ ≤ 2 * (18 * (p : ℝ) ^ (-2*s)) := by linarith
    _ = 36 * (p : ℝ) ^ (-2*s) := by ring

/-- Summability of |factor_p - 1| over primes p ≥ 5. -/
theorem prime_factor_sub_one_summable (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      |Real.exp ((-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))) - 1|) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 36 * (p : ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (36 : ℝ) * (p : ℝ) ^ (-2*s) =
        36 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 36
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => abs_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => prime_factor_sub_one_bound (p : ℕ) p.property.2 s hs z hz)
    hcomp

/-- The G₂ per-prime factor equals exp(correction_p). -/
theorem prime_factor_eq_exp (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    (1 - z * (p : ℝ) ^ (-s))⁻¹ * (1 - (p : ℝ) ^ (-s)) ^ z =
      Real.exp ((-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hza_lt : z * a < 1 := by
    have : |z * a| ≤ 2 / 3 := by
      rw [abs_mul, abs_of_pos ha_pos]
      have hmm : |z| * a ≤ 2 * (1 / 3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
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
      (1 - z * (p : ℝ) ^ (-s))⁻¹ * (1 - (p : ℝ) ^ (-s)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + (Real.exp ((-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
    | exact multipliable_one_add_of_summable (f := fun p => Real.exp ((-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))) - 1) hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - z * (p : ℝ) ^ (-s))⁻¹ * (1 - (p : ℝ) ^ (-s)) ^ z =
        1 + (Real.exp ((-Real.log (1 - z * (p : ℝ) ^ (-s))) + z * Real.log (1 - (p : ℝ) ^ (-s))) - 1) := by
    intro p
    have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
    rw [prime_factor_eq_exp (p : ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult

/-- The tail of G₂: infinite product over primes p≥5. -/
noncomputable def G2tail (s z : ℝ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (1 - z * (p : ℝ) ^ (-s))⁻¹ * (1 - (p : ℝ) ^ (-s)) ^ z

/-- G2tail actually has this product as its value, since the family is
    genuinely Multipliable. -/
theorem G2tail_hasProd (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (p : ℝ) ^ (-s))⁻¹ * (1 - (p : ℝ) ^ (-s)) ^ z) (G2tail s z) :=
  (prime_factor_multipliable s hs z hz).hasProd

/-- The full G₂(s,z): p=3 factor times the convergent tail over p≥5. -/
noncomputable def G2 (s z : ℝ) : ℝ :=
  (1 - z * (3 : ℝ) ^ (-s))⁻¹ * (1 - (3 : ℝ) ^ (-s)) ^ z * G2tail s z

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
  have hslit : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (t : ℂ) * w) ∈ Complex.slitPlane := by
    intro t ht
    have hre : (0 : ℝ) < (1 - (t : ℂ) * w).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      have h1 : t ≤ 1 := ht.2
      have h2 : (0 : ℝ) ≤ t := ht.1
      have h3 : t * w.re ≤ ‖w‖ := by
        have h4 := hre_le_norm w
        rw [abs_le] at h4
        nlinarith [h4.2]
      nlinarith [hw, h3]
    left; exact hre
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => -Complex.log (1 - (s : ℂ) * w)) (w / (1 - (t : ℂ) * w)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (1 : ℂ) - (s : ℂ) * w) (-w) t := by
      have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
        first
        | exact Complex.hasDerivAt_ofReal t
        | simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
        | exact (hasDerivAt_id t).ofReal_comp
      simpa using (hid.mul_const w).const_sub (1 : ℂ)
    have hslit_t := hslit t ht
    have hlogderiv : HasDerivAt Complex.log (1 - (t : ℂ) * w)⁻¹ (1 - (t : ℂ) * w) :=
      Complex.hasDerivAt_log hslit_t
    have h2 := hlogderiv.comp t h1
    have h3 : HasDerivAt (fun s : ℝ => -Complex.log (1 - (s : ℂ) * w))
        (-((1 - (t : ℂ) * w)⁻¹ * -w)) t := h2.neg
    have heq : -((1 - (t : ℂ) * w)⁻¹ * -w) = w / (1 - (t : ℂ) * w) := by
      rw [div_eq_mul_inv]; ring
    rwa [heq] at h3
  have hcont : ContinuousOn (fun t : ℝ => w / (1 - (t : ℂ) * w)) (Set.Icc 0 1) := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro t ht
      have := (hslit t ht)
      intro heq
      rw [heq] at this
      simp [Complex.slitPlane] at this
  have hFTC : ∫ t in (0 : ℝ)..1, w / (1 - (t : ℂ) * w) =
      (-Complex.log (1 - (1 : ℝ) * w)) - (-Complex.log (1 - (0 : ℝ) * w)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => -Complex.log (1 - (s : ℂ) * w))
      (f' := fun t : ℝ => w / (1 - (t : ℂ) * w))
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact hderiv t ht
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hcont
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, sub_zero,
    Complex.log_one, neg_zero, sub_zero] at hFTC
  have hintg : ∀ t ∈ Set.Icc (0 : ℝ) 1, w / (1 - (t : ℂ) * w) - w =
      (t : ℂ) * w^2 / (1 - (t : ℂ) * w) := by
    intro t ht
    have hne : (1 : ℂ) - (t : ℂ) * w ≠ 0 := by
      intro heq
      have := hslit t ht
      rw [heq] at this
      simp [Complex.slitPlane] at this
    rw [← sub_eq_zero]
    have step1 : w / (1 - (t : ℂ) * w) - (t : ℂ) * w^2 / (1 - (t : ℂ) * w) =
        (w - (t : ℂ) * w^2) / (1 - (t : ℂ) * w) := div_sub_div_same w ((t : ℂ) * w^2) _
    have step2 : w - (t : ℂ) * w^2 = w * (1 - (t : ℂ) * w) := by ring
    have step3 : w / (1 - (t : ℂ) * w) - w - (t : ℂ) * w^2 / (1 - (t : ℂ) * w) =
        (w / (1 - (t : ℂ) * w) - (t : ℂ) * w^2 / (1 - (t : ℂ) * w)) - w := by ring
    rw [step3, step1, step2, mul_div_assoc, div_self hne, mul_one]
    ring
  have hintconst : ∫ t in (0 : ℝ)..1, w = w := by
    simp [intervalIntegral.integral_const]
  have hsplit : ∫ t in (0 : ℝ)..1, (w / (1 - (t : ℂ) * w) - w) =
      ∫ t in (0 : ℝ)..1, ((t : ℂ) * w^2 / (1 - (t : ℂ) * w)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hintg t ht
  have hlhs : ∫ t in (0 : ℝ)..1, (w / (1 - (t : ℂ) * w) - w) = -Complex.log (1 - w) - w := by
    rw [intervalIntegral.integral_sub]
    · rw [hFTC, hintconst]
    · exact (hcont.mono (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ Set.Subset.refl _)).intervalIntegrable
    · exact intervalIntegrable_const
  have hkey : Complex.log (1 - w) + w = -(∫ t in (0 : ℝ)..1, ((t : ℂ) * w^2 / (1 - (t : ℂ) * w))) := by
    have h1 : -Complex.log (1 - w) - w = ∫ t in (0 : ℝ)..1, ((t : ℂ) * w^2 / (1 - (t : ℂ) * w)) := by
      rw [← hlhs, hsplit]
    linear_combination -h1
  rw [hkey, norm_neg]
  have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      ‖(t : ℂ) * w^2 / (1 - (t : ℂ) * w)‖ ≤ ‖w‖^2 / (1 - ‖w‖) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hne : (1 : ℂ) - (t : ℂ) * w ≠ 0 := by
      intro heq
      have := hslit t (Set.mem_Icc.mpr ⟨ht0, ht1⟩)
      rw [heq] at this
      simp [Complex.slitPlane] at this
    have hdenom : 1 - ‖w‖ ≤ ‖(1 : ℂ) - (t : ℂ) * w‖ := by
      have h1 : ((1 : ℂ) - (t : ℂ) * w).re ≤ ‖(1 : ℂ) - (t : ℂ) * w‖ := by
        have := hre_le_norm ((1 : ℂ) - (t : ℂ) * w)
        rw [abs_le] at this
        linarith [this.2]
      have h2 : 1 - ‖w‖ ≤ ((1 : ℂ) - (t : ℂ) * w).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im]
        have h3 : t * w.re ≤ ‖w‖ := by
          have h4 := hre_le_norm w
          rw [abs_le] at h4
          nlinarith [h4.2]
        nlinarith [h3]
      linarith
    have hdenom_pos : (0 : ℝ) < 1 - ‖w‖ := by linarith [hw]
    have htnorm : ‖(t : ℂ)‖ = t := by
      first
      | rw [Complex.norm_real]; exact abs_of_nonneg ht0
      | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ht0
      | simp [Complex.norm_eq_abs, abs_of_nonneg ht0]
    calc ‖(t : ℂ) * w^2 / (1 - (t : ℂ) * w)‖
        = t * ‖w‖^2 / ‖(1 : ℂ) - (t : ℂ) * w‖ := by
          rw [norm_div, norm_mul, norm_pow, htnorm]
      _ ≤ t * ‖w‖^2 / (1 - ‖w‖) := by
          apply div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom
      _ ≤ 1 * ‖w‖^2 / (1 - ‖w‖) := by
          apply div_le_div_of_nonneg_right _ hdenom_pos.le
          nlinarith [sq_nonneg ‖w‖, ht1]
      _ = ‖w‖^2 / (1 - ‖w‖) := by ring
  have hfinal := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := ‖w‖^2 / (1 - ‖w‖))
      (f := fun t : ℝ => (t : ℂ) * w^2 / (1 - (t : ℂ) * w))
      (fun t ht => hbound t (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact Set.Ioc_subset_Icc_self ht))
  simpa using hfinal

/-- Complex-z analogue of prime_correction_bound. -/
theorem prime_correction_bound_complex (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖
      ≤ 18 * (p : ℝ) ^ (-2*s) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z : ℂ) * (a : ℂ)‖ ≤ 2 / 3 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ 2 * (1 / 3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt1 : ‖(z : ℂ) * (a : ℂ)‖ < 1 := by linarith
  have hr1 := complex_log_bound ((z : ℂ) * (a : ℂ)) hza_lt1
  have hr2 := log_bound_combined a (by rw [abs_of_pos ha_pos]; linarith)
  have hr1bound : ‖z * (a : ℂ)‖^2 / (1 - ‖z * (a : ℂ)‖) ≤ 12 * a^2 := by
    have h1 : ‖z * (a : ℂ)‖ ≤ 2 * a := by
      rw [norm_mul, hane]; nlinarith [hz]
    have h2 : (1 : ℝ)/3 ≤ 1 - ‖z * (a : ℂ)‖ := by linarith [hza_le]
    have h3 : ‖z * (a : ℂ)‖^2 ≤ 4 * a^2 := by
      nlinarith [h1, norm_nonneg (z * (a : ℂ))]
    calc ‖z * (a : ℂ)‖^2 / (1 - ‖z * (a : ℂ)‖) ≤ ‖z * (a : ℂ)‖^2 / (1 / 3) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h2
      _ = 3 * ‖z * (a : ℂ)‖^2 := by ring
      _ ≤ 3 * (4 * a^2) := by linarith [h3]
      _ = 12 * a^2 := by ring
  have hkey : (-Complex.log (1 - z * (a : ℂ))) + z * (Real.log (1 - a) : ℂ)
      = -(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
          z * ((Real.log (1 - a) : ℂ) + (a : ℂ)) := by ring
  rw [hkey]
  have hstep1 : ‖-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖
      ≤ ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ := by
    have := norm_add_le (-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)))
      (z * ((Real.log (1 - a) : ℂ) + (a : ℂ)))
    rwa [norm_neg] at this
  have hstep2 : ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ ≤ ‖z‖ * (3 * a^2) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have heq : ((Real.log (1 - a) : ℂ) + (a : ℂ)) = ((Real.log (1 - a) + a : ℝ):ℂ) := by
      push_cast; ring
    rw [heq]
    first
    | rw [Complex.norm_real]; exact hr2
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact hr2
  have hfinal_bound : ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
      ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ ≤ 12 * a^2 + ‖z‖ * (3 * a^2) := by
    linarith [hr1, hr1bound, hstep2]
  calc ‖-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖
      ≤ ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ := hstep1
    _ ≤ 12 * a^2 + ‖z‖ * (3 * a^2) := hfinal_bound
    _ ≤ 12 * a^2 + 2 * (3 * a^2) := by nlinarith [hz, sq_nonneg a]
    _ = 18 * a^2 := by ring
    _ = 18 * (p : ℝ) ^ (-2*s) := by
        rw [ha_def, ← Real.rpow_natCast ((p : ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
        ring_nf

/-- Wide-radius variant: ||z|| <= 29 / 10 for p >= 5, constant 24.
Needed to place z = 2 strictly inside the disc of analyticity, which is what
sum 2^i c_i = d requires. -/
theorem prime_correction_bound_complex_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 29 / 10) :
    ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖
      ≤ 24 * (p : ℝ) ^ (-2*s) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 5 := by
    rw [ha_def]
    have hp3 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z : ℂ) * (a : ℂ)‖ ≤ 29 / 50 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ (29 / 10) * (1 / 5) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt1 : ‖(z : ℂ) * (a : ℂ)‖ < 1 := by linarith
  have hr1 := complex_log_bound ((z : ℂ) * (a : ℂ)) hza_lt1
  have hr2 := log_bound_combined_fifth a (by rw [abs_of_pos ha_pos]; linarith)
  have hr1bound : ‖z * (a : ℂ)‖^2 / (1 - ‖z * (a : ℂ)‖) ≤ (201 / 10) * a^2 := by
    have h1 : ‖z * (a : ℂ)‖ ≤ (29 / 10) * a := by
      rw [norm_mul, hane]; nlinarith [hz]
    have h2 : (21 : ℝ)/50 ≤ 1 - ‖z * (a : ℂ)‖ := by linarith [hza_le]
    have h3 : ‖z * (a : ℂ)‖^2 ≤ (841 / 100) * a^2 := by
      nlinarith [h1, norm_nonneg (z * (a : ℂ))]
    calc ‖z * (a : ℂ)‖^2 / (1 - ‖z * (a : ℂ)‖) ≤ ‖z * (a : ℂ)‖^2 / (21 / 50) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h2
      _ = (50 / 21) * ‖z * (a : ℂ)‖^2 := by ring
      _ ≤ (50 / 21) * ((841 / 100) * a^2) := by linarith [h3]
      _ ≤ (201 / 10) * a^2 := by nlinarith [sq_nonneg a]
  have hkey : (-Complex.log (1 - z * (a : ℂ))) + z * (Real.log (1 - a) : ℂ)
      = -(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
          z * ((Real.log (1 - a) : ℂ) + (a : ℂ)) := by ring
  rw [hkey]
  have hstep1 : ‖-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖
      ≤ ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ := by
    have := norm_add_le (-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)))
      (z * ((Real.log (1 - a) : ℂ) + (a : ℂ)))
    rwa [norm_neg] at this
  have hstep2 : ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ ≤ ‖z‖ * ((5 / 4) * a^2) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have heq : ((Real.log (1 - a) : ℂ) + (a : ℂ)) = ((Real.log (1 - a) + a : ℝ):ℂ) := by
      push_cast; ring
    rw [heq]
    first
    | rw [Complex.norm_real]; exact hr2
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact hr2
  have hfinal_bound : ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
      ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ ≤ (201 / 10) * a^2 + ‖z‖ * ((5 / 4) * a^2) := by
    linarith [hr1, hr1bound, hstep2]
  calc ‖-(Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)) +
        z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖
      ≤ ‖Complex.log (1 - z * (a : ℂ)) + z * (a : ℂ)‖ +
          ‖z * ((Real.log (1 - a) : ℂ) + (a : ℂ))‖ := hstep1
    _ ≤ (201 / 10) * a^2 + ‖z‖ * ((5 / 4) * a^2) := hfinal_bound
    _ ≤ (201 / 10) * a^2 + (29 / 10) * ((5 / 4) * a^2) := by nlinarith [hz, sq_nonneg a]
    _ ≤ 24 * a^2 := by nlinarith [sq_nonneg a]
    _ = 24 * (p : ℝ) ^ (-2*s) := by
        rw [ha_def, ← Real.rpow_natCast ((p : ℝ)^(-s)) 2, ← Real.rpow_mul hp0.le]
        ring_nf

/-- Complex-z analogue of prime_correction_summable. -/
theorem prime_correction_summable_complex (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => 18 * (p : ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (18 : ℝ) * (p : ℝ) ^ (-2*s) =
        18 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      prime_correction_bound_complex (p : ℕ) p.property.2 s hs z hz)
    hcomp

/-- Complex-z analogue of prime_factor_sub_one_bound. -/
theorem prime_factor_sub_one_bound_complex (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖
      ≤ 36 * (p : ℝ) ^ (-2*s) := by
  set c : ℂ := (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
    z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) with hc_def
  have hp3 : 3 ≤ p := by omega
  have hbound : ‖c‖ ≤ 18 * (p : ℝ) ^ (-2*s) := prime_correction_bound_complex p hp3 s hs z hz
  have hle1 : 18 * (p : ℝ) ^ (-2*s) ≤ 1 := correction_le_one p hp s hs
  have hc1 : ‖c‖ ≤ 1 := le_trans hbound hle1
  calc ‖Complex.exp c - 1‖ ≤ 2 * ‖c‖ := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (18 * (p : ℝ) ^ (-2*s)) := by linarith [hbound]
    _ = 36 * (p : ℝ) ^ (-2*s) := by ring

/-- Wide-radius variant: ||z|| <= 29 / 10, constant 48. -/
theorem prime_factor_sub_one_bound_complex_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 29 / 10) :
    ‖Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖
      ≤ 48 * (p : ℝ) ^ (-2*s) := by
  set c : ℂ := (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
    z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) with hc_def
  have hp3 : 5 ≤ p := by omega
  have hbound : ‖c‖ ≤ 24 * (p : ℝ) ^ (-2*s) := prime_correction_bound_complex_wide p hp3 s hs z hz
  have hle1 : 24 * (p : ℝ) ^ (-2*s) ≤ 1 := correction_le_one_wide p hp s hs
  have hc1 : ‖c‖ ≤ 1 := le_trans hbound hle1
  calc ‖Complex.exp c - 1‖ ≤ 2 * ‖c‖ := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (24 * (p : ℝ) ^ (-2*s)) := by linarith [hbound]
    _ = 48 * (p : ℝ) ^ (-2*s) := by ring

/-- Complex-z analogue of prime_factor_sub_one_summable. -/
theorem prime_factor_sub_one_summable_complex (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 36 * (p : ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (36 : ℝ) * (p : ℝ) ^ (-2*s) =
        36 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 36
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      prime_factor_sub_one_bound_complex (p : ℕ) p.property.2 s hs z hz)
    hcomp

/-- Complex-z analogue of prime_factor_eq_exp. -/
theorem prime_factor_eq_exp_complex (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
      Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z : ℂ) * (a : ℂ)‖ ≤ 2 / 3 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ 2 * (1 / 3) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt : ‖(z : ℂ) * (a : ℂ)‖ < 1 := by linarith
  have h1za_ne : (1 : ℂ) - z * (a : ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1 : ℝ) = ‖z * (a : ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)):ℂ) ^ z =
      Complex.exp (Complex.log (((1 - a : ℝ)):ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne]
  have key : Complex.exp ((-Complex.log (1 - z * (a : ℂ))) +
      z * ((Real.log (1 - a) : ℝ):ℂ)) =
      (1 - z * (a : ℂ))⁻¹ * (((1 - a : ℝ)):ℂ) ^ z := by
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_log h1za_ne, hcpow, ← hlog1a,
      show z * Complex.log (((1 - a : ℝ)):ℂ) = Complex.log (((1 - a : ℝ)):ℂ) * z
        from mul_comm _ _]
  exact key.symm

/-- Wide-radius variant. -/
theorem prime_factor_eq_exp_complex_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ ≤ 29 / 10) :
    (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
      Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 5 := by
    rw [ha_def]
    have hp3 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_le : ‖(z : ℂ) * (a : ℂ)‖ ≤ 29 / 50 := by
    rw [norm_mul, hane]
    have hmm : ‖z‖ * a ≤ (29 / 10) * (1 / 5) := mul_le_mul hz ha_le ha_pos.le (by norm_num)
    linarith
  have hza_lt : ‖(z : ℂ) * (a : ℂ)‖ < 1 := by linarith
  have h1za_ne : (1 : ℂ) - z * (a : ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1 : ℝ) = ‖z * (a : ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)):ℂ) ^ z =
      Complex.exp (Complex.log (((1 - a : ℝ)):ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne]
  have key : Complex.exp ((-Complex.log (1 - z * (a : ℂ))) +
      z * ((Real.log (1 - a) : ℝ):ℂ)) =
      (1 - z * (a : ℂ))⁻¹ * (((1 - a : ℝ)):ℂ) ^ z := by
    rw [Complex.exp_add, Complex.exp_neg, Complex.exp_log h1za_ne, hcpow, ← hlog1a,
      show z * Complex.log (((1 - a : ℝ)):ℂ) = Complex.log (((1 - a : ℝ)):ℂ) * z
        from mul_comm _ _]
  exact key.symm

/-- Complex-z analogue of prime_factor_multipliable. -/
theorem prime_factor_multipliable_complex (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable_complex s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + (Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
          (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
        1 + (Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1) := by
    intro p
    have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
    rw [prime_factor_eq_exp_complex (p : ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult

/-- Wide-radius variant (||z|| <= 29 / 10). -/
theorem prime_factor_sub_one_summable_complex_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 29 / 10) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1‖) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 48 * (p : ℝ) ^ (-2*s)) := by
    have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (48 : ℝ) * (p : ℝ) ^ (-2*s) =
        48 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 48
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      prime_factor_sub_one_bound_complex_wide (p : ℕ) p.property.2 s hs z hz)
    hcomp

/-- Wide-radius variant (||z|| <= 29 / 10). -/
theorem prime_factor_multipliable_complex_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 29 / 10) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hsummable := prime_factor_sub_one_summable_complex_wide s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + (Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1)) := by
    first
    | exact multipliable_one_add_of_summable hsummable
    | exact multipliable_one_add_of_summable_norm hsummable
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
          (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z =
        1 + (Complex.exp ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) - 1) := by
    intro p
    have hp3 : 5 ≤ (p : ℕ) := p.property.2
    rw [prime_factor_eq_exp_complex_wide (p : ℕ) hp3 s hs z hz]
    ring
  simpa only [heq] using hmult

/-- The complex-z tail of G₂: product over primes p≥5. -/
noncomputable def G2tailC (s : ℝ) (z : ℂ) : ℂ :=
  ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
    (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z

/-- G2tailC genuinely has this product as its value. -/
theorem G2tailC_hasProd (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z)
      (G2tailC s z) :=
  (prime_factor_multipliable_complex s hs z hz).hasProd

/-- Wide-radius variant: the tail product converges for ||z|| <= 29 / 10. -/
theorem G2tailC_hasProd_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 29 / 10) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ * ((((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ)) : ℂ)) ^ z)
      (G2tailC s z) :=
  (prime_factor_multipliable_complex_wide s hs z hz).hasProd

/-- The full complex G₂(s,z): p=3 factor times the convergent tail. -/
noncomputable def G2C (s : ℝ) (z : ℂ) : ℂ :=
  (1 - z * (((3 : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
    (((1 - (3 : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z * G2tailC s z

/-- The regularised factor collapses at z = 1. -/
theorem reg_factor_at_one (y : ℝ) (hy : (1 : ℝ) - y ≠ 0) :
    (1 - (1 : ℂ) * ((y : ℝ) : ℂ))⁻¹ * (((1 - y : ℝ)) : ℂ) ^ (1 : ℂ) = 1 := by
  rw [one_mul, Complex.cpow_one]
  have hcast : ((1 - y : ℝ) : ℂ) = 1 - ((y : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  have hne : (1 : ℂ) - ((y : ℝ) : ℂ) ≠ 0 := by
    rw [← hcast]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy
  field_simp

/-!
### G2at1 2 = d  (manuscript section 1, second identity)

Numerically verified: both sides are 0.37869502330363.

NOTE this is only the FUNCTION-VALUE half of "sum 2^i c_i = d".  The series
half needs z = 2 inside the disc of analyticity, and G2C_differentiableOn
currently gives ball 0 2 only, so that remains blocked on extending the
radius past 2 (see HANDOFF).

Decomposition:
  D1  per-factor: at z = 2, s = 1 the complex factor is the cast of the real
      factor (1 - 2/p)^(-1) (1 - 1/p)^2.
  D2  the real p >= 3 family is multipliable (same comparison as
      cFac_multipliable, with (1-2/p)^(-1) in place of (1-1/p)^(-1);
      needs p >= 5 or a per-prime check since 1 - 2 / 3 = 1 / 3 is small).
  D3  ofReal transfer, as in cFac_ofReal.
  D4  indicator-over-Nat.Primes = subtype-over-{p >= 3}, as in A3.
  D5  combine with the (1 / 2)^2 = 1 / 4 prefactor.
-/

/-- D1: at z = 2, s = 1 the regularised factor is the cast of the real one. -/
theorem reg_factor_at_two (y : ℝ) (hy : (1 : ℝ) - 2 * y ≠ 0) :
    (1 - (2 : ℂ) * ((y : ℝ) : ℂ))⁻¹ * (((1 - y : ℝ)) : ℂ) ^ (2 : ℂ)
      = ((((1 - 2*y : ℝ))⁻¹ * ((1 - y : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have hcast2 : ((1 - 2*y : ℝ) : ℂ) = 1 - (2 : ℂ) * ((y : ℝ) : ℂ) := by
    push_cast; ring
  have hne : (1 : ℂ) - (2 : ℂ) * ((y : ℝ) : ℂ) ≠ 0 := by
    rw [← hcast2]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy
  have hpow : (((1 - y : ℝ)) : ℂ) ^ (2 : ℂ) = (((1 - y : ℝ)) : ℂ) ^ (2 : ℕ) := by
    rw [← Complex.cpow_natCast]
    norm_num
  rw [hpow]
  push_cast
  field_simp

/-- G2tailC(1,1) = 1: every factor collapses. -/
theorem G2tailC_one_one : G2tailC 1 1 = 1 := by
  unfold G2tailC
  have hone : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      (1 - (1 : ℂ) * ((((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ))⁻¹
        * (((1 - ((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)) ^ (1 : ℂ) = 1 := by
    intro p
    have hp5 : (5 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
    have hlt : ((p : ℕ):ℝ) ^ (-(1 : ℝ)) < 1 := by
      rw [Real.rpow_neg_one]
      rw [inv_lt_one_iff₀]
      right
      linarith
    exact reg_factor_at_one (((p : ℕ):ℝ) ^ (-(1 : ℝ))) (by linarith)
  rw [funext hone, tprod_one]

/-- G2C(1,1) = 1 (manuscript section 1). -/
theorem G2C_one_one : G2C 1 1 = 1 := by
  unfold G2C
  rw [G2tailC_one_one, mul_one]
  have h3 : ((3 : ℝ)) ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    norm_num
  have := reg_factor_at_one (((3 : ℝ)) ^ (-(1 : ℝ))) (by linarith)
  rw [← this]
  norm_num

/-- Each G₂ per-prime factor is differentiable in z on |z|<2. -/
theorem prime_factor_differentiableOn (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
      (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) (Metric.ball 0 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza_lt : ‖z * (a : ℂ)‖ < 1 := by
    have hane : ‖(a : ℂ)‖ = a := by
      first
      | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
      | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
    rw [norm_mul, hane]
    nlinarith [hz, ha_le, ha_pos]
  have h1za_ne : (1 : ℂ) - z * (a : ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1 : ℝ) = ‖z * (a : ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · have hlin : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) - w * (a : ℂ)) z := by
      first
      | exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const (a : ℂ))
      | exact (differentiableAt_const (1 : ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a : ℂ))
    exact hlin.inv h1za_ne
  · first
    | exact differentiableAt_id.const_cpow (Or.inr h1a_ne)
    | exact differentiableAt_id.const_cpow (Or.inl h1a_ne)
    | exact DifferentiableAt.const_cpow differentiableAt_id (Or.inr h1a_ne)

/-- The p = 3 Euler factor is differentiable on the wide disc |z| < 29 / 10.
Simpler than the general per-prime lemma: no log estimates are needed, only
that 1 - z*3^(-s) is nonvanishing there (|z*3^(-s)| < 5 / 6 at s = 1) and that
the cpow factor is entire.  The general wide lemma requires p >= 5, so the
p = 3 factor of G2C needs this separate treatment. -/
theorem prime_three_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * ((((3 : ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ *
      ((((1 - ((3 : ℝ)) ^ (-s) : ℝ)) : ℂ)) ^ z) (Metric.ball 0 (29 / 10)) := by
  set a : ℝ := ((3 : ℝ)) ^ (-s) with ha_def
  have ha_pos : (0 : ℝ) < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have h1 : ((3 : ℝ)) ^ (-s) ≤ ((3 : ℝ)) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rw [Real.rpow_neg_one] at h1
    norm_num at h1
    linarith
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have h1a_ne : ((((1 - a : ℝ))) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza : Norm.norm (z * ((a : ℝ) : ℂ)) < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha_pos]
    calc Norm.norm z * a < (29 / 10) * a := by
          apply mul_lt_mul_of_pos_right hz ha_pos
      _ ≤ (29 / 10) * (1 / 3) := by
          apply mul_le_mul_of_nonneg_left ha_le (by norm_num)
      _ < 1 := by norm_num
  have hne : (1 : ℂ) - z * ((a : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have := sub_eq_zero.mp hcon
    rw [← this] at hza
    simp at hza
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w * ((a : ℝ) : ℂ)) z :=
      (differentiableAt_const 1).sub (differentiableAt_id.mul (differentiableAt_const _))
    exact hinner.inv hne
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl h1a_ne)

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
    DifferentiableOn ℂ (fun z : ℂ => (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
      z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) (Metric.ball 0 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_lt : ‖z * (a : ℂ)‖ < 1 := by
    rw [norm_mul, hane]; nlinarith [hz, ha_le, ha_pos]
  have hre_pos : (0 : ℝ) < ((1 : ℂ) - z * (a : ℂ)).re := by
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
      | exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const (a : ℂ))
      | exact (differentiableAt_const (1 : ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a : ℂ))
    · exact Or.inl hre_pos
  · exact differentiableAt_id.mul_const _

/-- The sum of correction terms is differentiable in z on |z|<2. -/
theorem correction_sum_differentiableOn (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)))
      (Metric.ball 0 2) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 18 * (p : ℝ) ^ (-2*s))
  · have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (18 : ℝ) * (p : ℝ) ^ (-2*s) =
        18 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  · intro p
    have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
    exact correction_differentiableOn (p : ℕ) hp3 s hs
  · exact Metric.isOpen_ball
  · intro p w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
    exact prime_correction_bound_complex (p : ℕ) hp3 s hs w hw.le

/-- G2tailC equals exp of the sum of correction terms. -/
theorem G2tailC_eq_exp_sum (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    G2tailC s z = Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  have hnormsum : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
    have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 18 * (p : ℝ) ^ (-2*s)) := by
      have h2s : -(2*s) < -1 := by linarith
      have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
        Real.summable_nat_rpow.mpr h2s
      have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
        hbase.subtype _
      have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (18 : ℝ) * (p : ℝ) ^ (-2*s) =
          18 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
        intro p; ring_nf
      simp_rw [heq]
      exact hsub.mul_left 18
    apply Summable.of_nonneg_of_le
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => by
        have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
        exact prime_correction_bound_complex (p : ℕ) hp3 s hs z hz)
      hcomp
  have hsummable : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) :=
    Summable.of_norm hnormsum
  have hhassum := hsummable.hasSum
  have hhasprod_exp := hasProd_exp_of_hasSum hhassum
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, Complex.exp
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z := by
    intro p
    have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
    exact (prime_factor_eq_exp_complex (p : ℕ) hp3 s hs z hz).symm
  simp only [heq] at hhasprod_exp
  have hhasprod_G2 := G2tailC_hasProd s hs z hz
  exact (hhasprod_G2.unique hhasprod_exp)

/-- G2tailC is differentiable on the ball |z|<2. -/
theorem G2tailC_differentiableOn (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2tailC s z) (Metric.ball 0 2) := by
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) 2, G2tailC s z = Complex.exp
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
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

/-- Wide-radius variant (radius 29 / 10, p >= 5). -/
theorem prime_factor_differentiableOn_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
      (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) (Metric.ball 0 (29 / 10)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 5 := by
    rw [ha_def]
    have hp3 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hza_lt : ‖z * (a : ℂ)‖ < 1 := by
    have hane : ‖(a : ℂ)‖ = a := by
      first
      | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
      | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
    rw [norm_mul, hane]
    nlinarith [hz, ha_le, ha_pos]
  have h1za_ne : (1 : ℂ) - z * (a : ℂ) ≠ 0 := by
    intro heq
    have h := sub_eq_zero.mp heq
    have hn : (1 : ℝ) = ‖z * (a : ℂ)‖ := by rw [← h]; simp
    linarith [hza_lt]
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · have hlin : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) - w * (a : ℂ)) z := by
      first
      | exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const (a : ℂ))
      | exact (differentiableAt_const (1 : ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a : ℂ))
    exact hlin.inv h1za_ne
  · first
    | exact differentiableAt_id.const_cpow (Or.inr h1a_ne)
    | exact differentiableAt_id.const_cpow (Or.inl h1a_ne)
    | exact DifferentiableAt.const_cpow differentiableAt_id (Or.inr h1a_ne)

/-- Wide-radius variant (radius 29 / 10, p >= 5). -/
theorem correction_differentiableOn_wide (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
      z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) (Metric.ball 0 (29 / 10)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 5 := by
    rw [ha_def]
    have hp3 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hane : ‖(a : ℂ)‖ = a := by
    first
    | rw [Complex.norm_real]; exact abs_of_nonneg ha_pos.le
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal]; exact abs_of_nonneg ha_pos.le
  have hza_lt : ‖z * (a : ℂ)‖ < 1 := by
    rw [norm_mul, hane]; nlinarith [hz, ha_le, ha_pos]
  have hre_pos : (0 : ℝ) < ((1 : ℂ) - z * (a : ℂ)).re := by
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
      | exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const (a : ℂ))
      | exact (differentiableAt_const (1 : ℂ)).sub (DifferentiableAt.mul_const differentiableAt_id (a : ℂ))
    · exact Or.inl hre_pos
  · exact differentiableAt_id.mul_const _

/-- Wide-radius variant (radius 29 / 10, p >= 5). -/
theorem correction_sum_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)))
      (Metric.ball 0 (29 / 10)) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 24 * (p : ℝ) ^ (-2*s))
  · have h2s : -(2*s) < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
      hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (24 : ℝ) * (p : ℝ) ^ (-2*s) =
        24 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 24
  · intro p
    have hp3 : 5 ≤ (p : ℕ) := p.property.2
    exact correction_differentiableOn_wide (p : ℕ) hp3 s hs
  · exact Metric.isOpen_ball
  · intro p w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hp3 : 5 ≤ (p : ℕ) := p.property.2
    exact prime_correction_bound_complex_wide (p : ℕ) hp3 s hs w hw.le

/-- Wide-radius variant (radius 29 / 10, p >= 5). -/
theorem G2tailC_eq_exp_sum_wide (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ ≤ 29 / 10) :
    G2tailC s z = Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  have hnormsum : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      ‖(-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)‖) := by
    have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 24 * (p : ℝ) ^ (-2*s)) := by
      have h2s : -(2*s) < -1 := by linarith
      have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*s))) :=
        Real.summable_nat_rpow.mpr h2s
      have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => ((p : ℕ):ℝ) ^ (-(2*s))) :=
        hbase.subtype _
      have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (24 : ℝ) * (p : ℝ) ^ (-2*s) =
          24 * ((p : ℕ):ℝ) ^ (-(2*s)) := by
        intro p; ring_nf
      simp_rw [heq]
      exact hsub.mul_left 24
    apply Summable.of_nonneg_of_le
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
      (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => by
        have hp3 : 5 ≤ (p : ℕ) := p.property.2
        exact prime_correction_bound_complex_wide (p : ℕ) hp3 s hs z hz)
      hcomp
  have hsummable : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) :=
    Summable.of_norm hnormsum
  have hhassum := hsummable.hasSum
  have hhasprod_exp := hasProd_exp_of_hasSum hhassum
  have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, Complex.exp
      ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z := by
    intro p
    have hp3 : 5 ≤ (p : ℕ) := p.property.2
    exact (prime_factor_eq_exp_complex_wide (p : ℕ) hp3 s hs z hz).symm
  simp only [heq] at hhasprod_exp
  have hhasprod_G2 := G2tailC_hasProd_wide s hs z hz
  exact (hhasprod_G2.unique hhasprod_exp)

/-- Wide-radius variant (radius 29 / 10, p >= 5). -/
theorem G2tailC_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2tailC s z) (Metric.ball 0 (29 / 10)) := by
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) (29 / 10), G2tailC s z = Complex.exp
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact G2tailC_eq_exp_sum_wide s hs z hz.le
  apply DifferentiableOn.congr _ heq
  exact Complex.differentiable_exp.comp_differentiableOn (correction_sum_differentiableOn_wide s hs)

/-- Wide-radius variant (radius 29 / 10, p >= 5). -/
theorem G2C_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (fun z => G2C s z) (Metric.ball 0 (29 / 10)) := by
  unfold G2C
  apply DifferentiableOn.mul
  · exact prime_three_differentiableOn_wide s hs
  · exact G2tailC_differentiableOn_wide s hs

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
    (1 - (starRingEnd ℂ) z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ *
        (((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have h1a_ne : (((1 - a : ℝ)):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hlog1a : Complex.log (((1 - a : ℝ)):ℂ) = ((Real.log (1-a) : ℝ):ℂ) := by
    rw [Complex.ofReal_log h1a_pos.le]
  have hlog1a_real : (starRingEnd ℂ) (Complex.log (((1 - a : ℝ)):ℂ)) =
      Complex.log (((1 - a : ℝ)):ℂ) := by
    rw [hlog1a]; exact Complex.conj_ofReal _
  have hane_conj : (starRingEnd ℂ) ((a : ℂ)) = (a : ℂ) := Complex.conj_ofReal _
  have hcpow_symm : (((1 - a : ℝ)):ℂ) ^ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((((1 - a : ℝ)):ℂ) ^ z) := by
    rw [Complex.cpow_def_of_ne_zero h1a_ne, Complex.cpow_def_of_ne_zero h1a_ne,
      ← Complex.exp_conj]
    congr 1
    rw [map_mul, hlog1a_real]
  have hinv_symm : (1 - (starRingEnd ℂ) z * (a : ℂ))⁻¹ =
      (starRingEnd ℂ) ((1 - z * (a : ℂ))⁻¹) := by
    rw [map_inv₀, map_sub, map_one, map_mul, hane_conj]
  rw [hcpow_symm, hinv_symm, ← map_mul]

/-- Each per-prime correction term satisfies conjugate-reflection symmetry
    on the ball |z|<2. -/
theorem correction_conj_symm (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : ‖z‖ < 2) :
    (-Complex.log (1 - (starRingEnd ℂ) z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        (starRingEnd ℂ) z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) =
      (starRingEnd ℂ) ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set a : ℝ := (p : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le : a ≤ 1 / 3 := by
    rw [ha_def]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : (p : ℝ) ^ (-1:ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / (p : ℝ) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith
  have h1a_pos : (0 : ℝ) < 1 - a := by linarith
  have hlog1a_real : (starRingEnd ℂ) ((Real.log (1 - a) : ℝ):ℂ) =
      ((Real.log (1 - a) : ℝ):ℂ) := Complex.conj_ofReal _
  have hane_conj : (starRingEnd ℂ) ((a : ℂ)) = (a : ℂ) := Complex.conj_ofReal _
  have hre_pos : ∀ w : ℂ, ‖w‖ < 2 → (0 : ℝ) < ((1 : ℂ) - w * (a : ℂ)).re := by
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
      ((1 : ℂ) - w * (a : ℂ)).arg ≠ Real.pi := by
    intro w hw harg
    have := hre_pos w hw
    rw [Complex.arg_eq_pi_iff] at harg
    linarith [harg.1]
  have hlog_conj : Complex.log ((starRingEnd ℂ) (1 - z * (a : ℂ))) =
      (starRingEnd ℂ) (Complex.log (1 - z * (a : ℂ))) := by
    rw [Complex.log_conj (1 - z * (a : ℂ)) (harg_ne z hz)]
  have hconj_sub : (starRingEnd ℂ) (1 - z * (a : ℂ)) = 1 - (starRingEnd ℂ) z * (a : ℂ) := by
    rw [map_sub, map_one, map_mul, hane_conj]
  rw [← hconj_sub, hlog_conj]
  simp only [map_neg, map_add, map_mul, hlog1a_real]

/-- The correction-term sum satisfies conjugate-reflection symmetry. -/
theorem correction_sum_conj_symm (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : ‖z‖ < 2) :
    ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ((-Complex.log (1 - (starRingEnd ℂ) z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
        (starRingEnd ℂ) z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ)) =
      (starRingEnd ℂ) (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ((-Complex.log (1 - z * (((p : ℝ) ^ (-s) : ℝ) : ℂ))) +
          z * ((Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ))) := by
  rw [RCLike.conj_tsum]
  apply tsum_congr
  intro p
  have hp3 : 3 ≤ (p : ℕ) := by have := p.property.2; omega
  exact correction_conj_symm (p : ℕ) hp3 s hs z hz

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
  have hcast : ((3 : ℕ):ℝ) = (3 : ℝ) := by norm_num
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
  have hUopen : IsOpen (Metric.ball (0 : ℂ) 2) := Metric.isOpen_ball
  have hUconj : ∀ w ∈ Metric.ball (0 : ℂ) 2, (starRingEnd ℂ) w ∈ Metric.ball (0 : ℂ) 2 := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    rwa [Complex.norm_conj]
  have hf : DifferentiableOn ℂ (fun z => G2C s z) (Metric.ball (0 : ℂ) 2) :=
    G2C_differentiableOn s hs
  have hsymm : ∀ w ∈ Metric.ball (0 : ℂ) 2,
      G2C s ((starRingEnd ℂ) w) = (starRingEnd ℂ) (G2C s w) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact G2C_conj_symm s hs w hw
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
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
        push Not at h
        interval_cases (n / p)
        · simp [bigOmega] at hnpk; omega
        · have : bigOmega 1 = 0 := by simp [bigOmega]
          omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnp2, ?_⟩, hnpk, ?_⟩
      · have hcast : ((n / p : ℕ) : ℝ) = (n : ℝ) / p := by
          rw [eq_div_iff (by positivity)]
          exact_mod_cast Nat.div_mul_cancel hpdvd
        rw [Nat.le_floor_iff (by positivity), hcast]
        calc (n : ℝ)/p ≤ (⌊x⌋₊:ℝ)/p := by
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
        have : (m : ℝ) ≤ x / p := hmx
        have hpm : (p * m : ℝ) ≤ x := by
          rw [le_div_iff₀ (by positivity)] at this
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
      push Not at h
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
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have h2 : Real.log (primorial n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := by
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
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc Real.sqrt n ≤ Real.sqrt (n*n) := by
          apply Real.sqrt_le_sqrt; nlinarith [hn1]
      _ = n := by rw [show (n : ℝ)*n = n^2 by ring, Real.sqrt_sq (by positivity)]
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
      push Not at h
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
    have : (2 : ℝ) ≤ Real.sqrt n := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
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
          linarith [Nat.floor_le (show (0 : ℝ) ≤ x by linarith)]
        linarith
      have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hfloor2 : (2 : ℝ) ≤ ⌊x⌋₊ := by linarith
      have hlogfloor_pos : 0 < Real.log ⌊x⌋₊ := Real.log_pos (by exact_mod_cast hfloor2)
      have hlog4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx4
      have hlogfloor_ge : Real.log ⌊x⌋₊ ≥ Real.log x / 2 := by
        have hge : Real.log ⌊x⌋₊ ≥ Real.log (x / 2) := Real.log_le_log (by linarith) hfloor_ge
        have heq : Real.log (x / 2) = Real.log x - Real.log 2 := by
          rw [Real.log_div (by linarith) (by norm_num)]
        have hlog2 : Real.log 2 ≤ Real.log x / 2 := by
          have : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; ring
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
          have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          linarith
        have hnn : (0 : ℝ) ≤ 4 * (⌊x⌋₊:ℝ) * (1 + Real.log 4) := by
          have : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg ⌊x⌋₊
          nlinarith [this, hpos]
        nlinarith [mul_le_mul_of_nonneg_left hlogfloor_ge hnn]
      have hxbound : 4 * ⌊x⌋₊ * (1 + Real.log 4) / Real.log x ≤
          4 * x * (1 + Real.log 4) / Real.log x := by
        have hpos : (0 : ℝ) ≤ (1 + Real.log 4) := by
          have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
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
      have hbound_small : (3 : ℝ) / Real.log 4 ≤ x / Real.log x := by
        rw [div_le_div_iff₀ hlog4_pos hlogx_pos]
        nlinarith [hlogx_le, hx]
      have h2le : (2 : ℝ) ≤ (2 + 4 * Real.log 4 + 10) * (3 / Real.log 4) := by
        rw [← mul_div_assoc, le_div_iff₀ hlog4_pos]
        nlinarith [hlog4_pos]
      have hstep : (2 + 4 * Real.log 4 + 10) * (3 / Real.log 4) ≤
          (2 + 4 * Real.log 4 + 10) * (x / Real.log x) := by
        apply mul_le_mul_of_nonneg_left hbound_small
        positivity
      have hfinal2 : (2 : ℝ) ≤ (2 + 4 * Real.log 4 + 10) * x / Real.log x := by
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
    push Not at hxle
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

/-- h(t) = (x/t)/log(x/t) is antitone on [1, x / 3]. Extracted from the argument
inside `h_p0_bound` so it can be reused per dyadic fiber. -/
theorem ratio_log_antitoneOn (x : ℝ) (hx : 3 ≤ x) :
    AntitoneOn (fun s => (x / s) / Real.log (x / s)) (Set.Icc (1 : ℝ) (x / 3)) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hconv : Convex ℝ (Set.Icc (1 : ℝ) (x / 3)) := convex_Icc _ _
  have hint_eq : interior (Set.Icc (1 : ℝ) (x / 3)) = Set.Ioo (1 : ℝ) (x / 3) := interior_Icc
  have hxt3_of : ∀ t, 1 ≤ t → t ≤ x / 3 → (3 : ℝ) ≤ x / t := by
    intro t ht1 ht2
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) ≤ x / t := div_le_div_of_nonneg_left hxpos.le htpos ht2
    linarith [heq3 ▸ hge]
  have hcont : ContinuousOn (fun s => (x/s)/Real.log (x/s)) (Set.Icc (1 : ℝ) (x / 3)) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht.1
    have hxt3 := hxt3_of t ht.1 ht.2
    exact (differentiableAt_ratio_log x t htpos (by linarith)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (x/s)/Real.log (x/s))
      (interior (Set.Icc (1 : ℝ) (x / 3))) := by
    rw [hint_eq]
    intro t ht
    simp only [Set.mem_Ioo] at ht
    have htpos : 0 < t := lt_trans one_pos ht.1
    have hxt3 := hxt3_of t ht.1.le ht.2.le
    exact (differentiableAt_ratio_log x t htpos (by linarith)).differentiableWithinAt
  have hderiv_np : ∀ t ∈ interior (Set.Icc (1 : ℝ) (x / 3)),
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
      have hl3 : (1 : ℝ) < Real.log 3 := by
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hloge1
      linarith
    have hnum_neg : (1 : ℝ) - Real.log (x/t) < 0 := by linarith
    have hden_pos : (0 : ℝ) < (Real.log (x/t))^2 := by positivity
    have hxt2_pos : (0 : ℝ) < x/t^2 := by positivity
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
  have hxpos : (0 : ℝ) < x := by linarith
  have h2jpos : (0 : ℝ) < (2 ^ j : ℝ) := by positivity
  have hx2j3 : (3 : ℝ) ≤ x / (2 ^ j : ℝ) := by
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) ≤ x / (2 ^ j : ℝ) :=
      div_le_div_of_nonneg_left hxpos.le h2jpos h2j
    linarith [heq3 ▸ hge]
  have hlogpos : 0 < Real.log (x / (2 ^ j : ℝ)) := Real.log_pos (by linarith)
  have hb_nonneg : 0 ≤ (x / (2 ^ j : ℝ)) / Real.log (x / (2 ^ j : ℝ)) :=
    div_nonneg (div_nonneg hxpos.le h2jpos.le) hlogpos.le
  have h1le2j : (1 : ℝ) ≤ (2 ^ j : ℝ) := by
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
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
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
The sqrt term is absorbed via sqrt(n)*log(sqrt(n)) ≤ n and log 2 > 1 / 2. -/
theorem primeCounting_two_pow_bound (j : ℕ) (hj : 1 ≤ j) :
    (Nat.primeCounting (2 ^ (j + 1)) : ℝ) ≤ 8 * 2 ^ (j + 1) / (j + 1) := by
  have hn4 : 4 ≤ 2 ^ (j + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmain := primeCounting_le_bound_own (2 ^ (j + 1)) hn4
  have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by norm_cast
  rw [hcast] at hmain
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsqrt : Real.log (Real.sqrt ((2 : ℝ) ^ (j + 1)))
      = ((j : ℝ) + 1) * Real.log 2 / 2 := by
    rw [Real.log_sqrt h2pos.le, Real.log_pow]
    push_cast
    try ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hterm2 : (2 : ℝ) ^ (j + 1) * Real.log 4 / Real.log (Real.sqrt ((2 : ℝ) ^ (j + 1)))
      = 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1) := by
    rw [hlogsqrt, hlog4]
    have hne1 : ((j : ℝ) + 1) ≠ 0 := hj1pos.ne'
    have hne2 : Real.log 2 ≠ 0 := hlog2pos.ne'
    field_simp
    try ring
  have hs_nonneg : 0 ≤ Real.sqrt ((2 : ℝ) ^ (j + 1)) := Real.sqrt_nonneg _
  have hlog2_half : (1 : ℝ)/2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hsqrt_bound : Real.sqrt ((2 : ℝ) ^ (j + 1))
      ≤ 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1) := by
    have hlog_le : Real.log (Real.sqrt ((2 : ℝ) ^ (j + 1)))
        ≤ Real.sqrt ((2 : ℝ) ^ (j + 1)) := Real.log_le_self hs_nonneg
    have hsq : Real.sqrt ((2 : ℝ) ^ (j + 1)) * Real.sqrt ((2 : ℝ) ^ (j + 1))
        = (2 : ℝ) ^ (j + 1) := Real.mul_self_sqrt h2pos.le
    have hkey : Real.sqrt ((2 : ℝ) ^ (j + 1)) * (((j : ℝ) + 1) * Real.log 2 / 2)
        ≤ (2 : ℝ) ^ (j + 1) := by
      rw [← hlogsqrt]
      calc Real.sqrt ((2 : ℝ) ^ (j + 1)) * Real.log (Real.sqrt ((2 : ℝ) ^ (j + 1)))
          ≤ Real.sqrt ((2 : ℝ) ^ (j + 1)) * Real.sqrt ((2 : ℝ) ^ (j + 1)) :=
            mul_le_mul_of_nonneg_left hlog_le hs_nonneg
        _ = (2 : ℝ) ^ (j + 1) := hsq
    rw [le_div_iff₀ hj1pos]
    nlinarith [hkey, hs_nonneg, hj1pos, hlog2_half,
      mul_nonneg (mul_nonneg hs_nonneg hj1pos.le) (sub_nonneg.mpr hlog2_half)]
  rw [hterm2] at hmain
  have h48 : 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1) + 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)
      = 8 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1) := by ring
  linarith [hmain, hsqrt_bound, h48]

/-- Per-fiber constant simplification:
h(2^j) * pi(2^(j+1)) ≤ 16*x / ((j+1) * log(x / 2^j)). -/
theorem dyadic_term_bound (x : ℝ) (j : ℕ) (hj : 1 ≤ j) (hx : 9 ≤ x)
    (h2j : (2 : ℝ) ^ j ≤ x / 3) :
    ((x / (2 : ℝ) ^ j) / Real.log (x / (2 : ℝ) ^ j)) *
        (Nat.primeCounting (2 ^ (j + 1)) : ℝ) ≤
      16 * x / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hx2j3 : (3 : ℝ) ≤ x / (2 : ℝ) ^ j := by
    have heq3 : x / (x / 3) = 3 := by field_simp
    have hge : x / (x / 3) ≤ x / (2 : ℝ) ^ j :=
      div_le_div_of_nonneg_left hxpos.le h2jpos h2j
    linarith [heq3 ▸ hge]
  have hlogpos : (0 : ℝ) < Real.log (x / (2 : ℝ) ^ j) := Real.log_pos (by linarith)
  have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hh_nonneg : (0 : ℝ) ≤ (x / (2 : ℝ) ^ j) / Real.log (x / (2 : ℝ) ^ j) :=
    div_nonneg (by positivity) hlogpos.le
  have hpc := primeCounting_two_pow_bound j hj
  have hid : ((x / (2 : ℝ) ^ j) / Real.log (x / (2 : ℝ) ^ j)) *
      (8 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1))
      = 16 * x / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := by
    have hne1 : ((j : ℝ) + 1) ≠ 0 := hj1pos.ne'
    have hne2 : Real.log (x / (2 : ℝ) ^ j) ≠ 0 := hlogpos.ne'
    have hne3 : (2 : ℝ) ^ j ≠ 0 := h2jpos.ne'
    rw [pow_succ]
    field_simp
    try ring
  calc ((x / (2 : ℝ) ^ j) / Real.log (x / (2 : ℝ) ^ j)) *
      (Nat.primeCounting (2 ^ (j + 1)) : ℝ)
      ≤ ((x / (2 : ℝ) ^ j) / Real.log (x / (2 : ℝ) ^ j)) *
        (8 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hpc hh_nonneg
    _ = 16 * x / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := hid

/-- On the low dyadic range ((2^j)^2 ≤ x): log(x / 2^j) ≥ (log x)/2. -/
theorem log_ratio_low (x : ℝ) (j : ℕ) (hx : 9 ≤ x)
    (hsq : ((2 : ℝ) ^ j) ^ 2 ≤ x) :
    Real.log x / 2 ≤ Real.log (x / (2 : ℝ) ^ j) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have h2j_le_sqrt : (2 : ℝ) ^ j ≤ Real.sqrt x := by
    rw [show ((2 : ℝ) ^ j) = Real.sqrt (((2 : ℝ) ^ j) ^ 2) by
      rw [Real.sqrt_sq h2jpos.le]]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hdiv : Real.sqrt x ≤ x / (2 : ℝ) ^ j := by
    rw [le_div_iff₀ h2jpos]
    calc Real.sqrt x * (2 : ℝ) ^ j ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h2j_le_sqrt hsqrt_pos.le
      _ = x := Real.mul_self_sqrt hxpos.le
  calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hxpos.le).symm
    _ ≤ Real.log (x / (2 : ℝ) ^ j) := Real.log_le_log hsqrt_pos hdiv

/-- Harmonic sum bound, real form: sum_(i<n) 1/(i+1) ≤ 1 + log n. -/
theorem harmonic_sum_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log n := by
  have heq : ((harmonic n : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) := by
    unfold harmonic
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div]
  rw [← heq]
  exact harmonic_le_one_add_log n


/-- Flip helper: B ≤ x / 3 gives 3 ≤ x/B (dedups a pattern used repeatedly). -/
theorem div_ge_three_of_le_third (x B : ℝ) (hxpos : 0 < x) (hB : 0 < B)
    (h : B ≤ x / 3) : 3 ≤ x / B := by
  have heq3 : x / (x / 3) = 3 := by field_simp
  have hge : x / (x / 3) ≤ x / B := div_le_div_of_nonneg_left hxpos.le hB h
  linarith [heq3 ▸ hge]

/-- For x ≥ 9 we have log x ≥ 2, via e^2 < 7.4 < 9. -/
theorem two_le_log (x : ℝ) (hx : 9 ≤ x) : (2 : ℝ) ≤ Real.log x := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have he2 : Real.exp 2 ≤ x := by
    rw [h2]
    nlinarith [(Real.exp_pos 1).le, h1, hx]
  rw [show (2 : ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
  exact Real.log_le_log (Real.exp_pos 2) he2

/-- For x ≥ 9, loglog x ≥ log 2. -/
theorem loglog_ge_log_two (x : ℝ) (hx : 9 ≤ x) :
    Real.log 2 ≤ Real.log (Real.log x) := by
  have h2 := two_le_log x hx
  exact Real.log_le_log (by norm_num) (by linarith)

/-- The dyadic index J = Nat.log 2 (floor(x / 3)) brackets x / 3 between 2^J and 2^(J+1). -/
theorem dyadic_log_bounds (x : ℝ) (hx : 9 ≤ x) :
    (2 : ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊) ≤ x / 3 ∧
      x / 3 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) := by
  have hx3 : (3 : ℝ) ≤ x / 3 := by linarith
  have hN : 3 ≤ ⌊x / 3⌋₊ := Nat.le_floor (by push_cast; linarith)
  constructor
  · have h1 : (2 : ℕ) ^ (Nat.log 2 ⌊x / 3⌋₊) ≤ ⌊x / 3⌋₊ :=
      Nat.pow_log_le_self 2 (by omega)
    have h2 : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
    calc (2 : ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊)
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
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊x / 3⌋₊ + 1) := by norm_cast

/-- If x / 3 ≤ 2^(J+1) then (J+1)*log 2 ≥ (log x)/2, via sqrt x ≤ x / 3 for x ≥ 9. -/
theorem log_x_half_le (x : ℝ) (J : ℕ) (hx : 9 ≤ x)
    (hJ : x / 3 ≤ (2 : ℝ) ^ (J + 1)) :
    Real.log x / 2 ≤ ((J : ℝ) + 1) * Real.log 2 := by
  have hxpos : (0 : ℝ) < x := by linarith
  have h3sqrt : (3 : ℝ) ≤ Real.sqrt x := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsqrt_le : Real.sqrt x ≤ x / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    calc Real.sqrt x * 3 ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h3sqrt (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hxpos.le
  calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hxpos.le).symm
    _ ≤ Real.log ((2 : ℝ) ^ (J + 1)) :=
        Real.log_le_log (Real.sqrt_pos.mpr hxpos) (le_trans hsqrt_le hJ)
    _ = ((J : ℝ) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        try ring

/-- If 2^J ≤ x then J+1 ≤ 2*log x, for x ≥ 9. -/
theorem J_le_two_log (x : ℝ) (J : ℕ) (hx : 9 ≤ x)
    (hJ : (2 : ℝ) ^ J ≤ x) : ((J : ℝ) + 1) ≤ 2 * Real.log x := by
  have hlogx2 := two_le_log x hx
  have hJlog : (J : ℝ) * Real.log 2 ≤ Real.log x := by
    calc (J : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ J) := by rw [Real.log_pow]
      _ ≤ Real.log x := Real.log_le_log (by positivity) hJ
  have hlog2_23 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hJle : (J : ℝ) ≤ (3 / 2) * Real.log x := by
    have h1 : (J : ℝ) * ((2 : ℝ) / 3) ≤ (J : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2_23 (by positivity)
    nlinarith [hJlog]
  linarith [hJle, hlogx2]

/-- The final constant absorption: 1 + log(J+1) ≤ 4*loglog x when J+1 ≤ 2*log x. -/
theorem one_add_log_le_loglog (x : ℝ) (J : ℕ) (hx : 9 ≤ x)
    (hJ2 : ((J : ℝ) + 1) ≤ 2 * Real.log x) :
    1 + Real.log ((J : ℝ) + 1) ≤ 4 * Real.log (Real.log x) := by
  have hlogx2 := two_le_log x hx
  have hloglog := loglog_ge_log_two x hx
  have hJ1pos : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hA : Real.log ((J : ℝ) + 1) ≤ Real.log 2 + Real.log (Real.log x) := by
    calc Real.log ((J : ℝ) + 1) ≤ Real.log (2 * Real.log x) :=
          Real.log_le_log hJ1pos hJ2
      _ = Real.log 2 + Real.log (Real.log x) := Real.log_mul (by norm_num) (by linarith)
  have hB : (1 : ℝ) ≤ 2 * Real.log 2 := by
    have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) he
      _ = 2 * Real.log 2 := h4
  linarith [hA, hB, hloglog]

/-- Low dyadic range (j ≤ M, 2M ≤ J): harmonic bound with the (log x)/2 floor. -/
theorem dyadic_low_sum (x : ℝ) (J M : ℕ) (hx : 9 ≤ x) (hM : 2 * M ≤ J)
    (hJ : (2 : ℝ) ^ J ≤ x) :
    ∑ j ∈ Finset.range (M + 1), 1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      ≤ 2 / Real.log x * (1 + Real.log ((M : ℝ) + 1)) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hc_nonneg : (0 : ℝ) ≤ 2 / Real.log x := by positivity
  have hterm : ∀ j ∈ Finset.range (M + 1),
      1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
        ≤ 2 / Real.log x * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hsq : ((2 : ℝ) ^ j) ^ 2 ≤ x := by
      have h1 : ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (j * 2) := (pow_mul 2 j 2).symm
      rw [h1]
      calc (2 : ℝ) ^ (j * 2) ≤ (2 : ℝ) ^ J := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
        _ ≤ x := hJ
    have hlow := log_ratio_low x j hx hsq
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hden1 : (0 : ℝ) < ((j : ℝ) + 1) * (Real.log x / 2) := by positivity
    have hmono : ((j : ℝ) + 1) * (Real.log x / 2)
        ≤ ((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hlow hj1.le
    have h1 := one_div_le_one_div_of_le hden1 hmono
    have h2 : 1 / (((j : ℝ) + 1) * (Real.log x / 2))
        = 2 / Real.log x * (1 / ((j : ℝ) + 1)) := by
      have hne1 : ((j : ℝ) + 1) ≠ 0 := hj1.ne'
      have hne2 : Real.log x ≠ 0 := hlogx_pos.ne'
      field_simp
      try ring
    calc 1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
        ≤ 1 / (((j : ℝ) + 1) * (Real.log x / 2)) := h1
      _ = 2 / Real.log x * (1 / ((j : ℝ) + 1)) := h2
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : ∑ j ∈ Finset.range (M + 1), 2 / Real.log x * (1 / ((j : ℝ) + 1))
      = 2 / Real.log x * ∑ j ∈ Finset.range (M + 1), (1 / ((j : ℝ) + 1)) := by
    rw [Finset.mul_sum]
  have hharm := harmonic_sum_le (M + 1)
  have hcastlog : Real.log ((M + 1 : ℕ) : ℝ) = Real.log ((M : ℝ) + 1) := by norm_cast
  calc ∑ j ∈ Finset.range (M + 1),
      1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      ≤ ∑ j ∈ Finset.range (M + 1), 2 / Real.log x * (1 / ((j : ℝ) + 1)) := hsum1
    _ = 2 / Real.log x * ∑ j ∈ Finset.range (M + 1), (1 / ((j : ℝ) + 1)) := hsum2
    _ ≤ 2 / Real.log x * (1 + Real.log ((M : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nonneg
        calc ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1)
            ≤ 1 + Real.log ((M + 1 : ℕ) : ℝ) := hharm
          _ = 1 + Real.log ((M : ℝ) + 1) := by rw [hcastlog]

/-- High dyadic range (M < j ≤ J, J ≤ 2M+1): reflected harmonic bound. -/
theorem dyadic_high_sum (x : ℝ) (J M : ℕ) (hx : 9 ≤ x) (hJM : J ≤ 2 * M + 1)
    (hJ3 : (2 : ℝ) ^ J ≤ x / 3) :
    ∑ j ∈ Finset.Ico (M + 1) (J + 1),
        1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      ≤ 2 / (((J : ℝ) + 1) * Real.log 2) * (1 + Real.log ((J : ℝ) + 1)) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hJ1pos : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have hc_nonneg : (0 : ℝ) ≤ 2 / (((J : ℝ) + 1) * Real.log 2) := by positivity
  have hterm : ∀ j ∈ Finset.Ico (M + 1) (J + 1),
      1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
        ≤ 2 / (((J : ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hjJ : j ≤ J := by omega
    have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h2Jpos : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
    have hx2J : (3 : ℝ) ≤ x / (2 : ℝ) ^ J :=
      div_ge_three_of_le_third x ((2 : ℝ) ^ J) hxpos h2Jpos hJ3
    have hsplit : x / (2 : ℝ) ^ j = (x / (2 : ℝ) ^ J) * (2 : ℝ) ^ (J - j) := by
      have hpow : (2 : ℝ) ^ J = (2 : ℝ) ^ j * (2 : ℝ) ^ (J - j) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
      try ring
    have hx2j_ge : (2 : ℝ) ^ ((J - j) + 1) ≤ x / (2 : ℝ) ^ j := by
      rw [hsplit, pow_succ]
      have h2 : (2 : ℝ) ≤ x / (2 : ℝ) ^ J := by linarith
      calc (2 : ℝ) ^ (J - j) * 2 ≤ (2 : ℝ) ^ (J - j) * (x / (2 : ℝ) ^ J) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (x / (2 : ℝ) ^ J) * (2 : ℝ) ^ (J - j) := mul_comm _ _
    have hlog_ge : ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2
        ≤ Real.log (x / (2 : ℝ) ^ j) := by
      have h1 : Real.log ((2 : ℝ) ^ ((J - j) + 1))
          = ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        try ring
      calc ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2
          = Real.log ((2 : ℝ) ^ ((J - j) + 1)) := h1.symm
        _ ≤ Real.log (x / (2 : ℝ) ^ j) := Real.log_le_log (by positivity) hx2j_ge
    have hfrac : ((J : ℝ) + 1) / 2 ≤ (j : ℝ) + 1 := by
      have hn : J + 1 ≤ 2 * (j + 1) := by omega
      have hcast := (Nat.cast_le (α := ℝ)).mpr hn
      push_cast at hcast
      linarith
    have hlog_pos_j : (0 : ℝ) < Real.log (x / (2 : ℝ) ^ j) := by
      have h1 : (0 : ℝ) < ((((J - j : ℕ) : ℝ)) + 1) * Real.log 2 := by positivity
      linarith [hlog_ge]
    have hden_lower : (0 : ℝ) <
        ((J : ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2) := by
      positivity
    have hden_ge : ((J : ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2)
        ≤ ((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j) :=
      mul_le_mul hfrac hlog_ge (by positivity) (by positivity)
    have h1 := one_div_le_one_div_of_le hden_lower hden_ge
    have h2 : 1 / (((J : ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2))
        = 2 / (((J : ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := by
      have hne1 : ((J : ℝ) + 1) ≠ 0 := hJ1pos.ne'
      have hne2 : Real.log 2 ≠ 0 := hlog2_pos.ne'
      have hne3 : ((((J - j : ℕ) : ℝ)) + 1) ≠ 0 := by positivity
      field_simp
      try ring
    calc 1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
        ≤ 1 / (((J : ℝ) + 1) / 2 * (((((J - j : ℕ) : ℝ)) + 1) * Real.log 2)) := h1
      _ = 2 / (((J : ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := h2
  have hsum1 := Finset.sum_le_sum hterm
  have hsum2 : ∑ j ∈ Finset.Ico (M + 1) (J + 1),
      2 / (((J : ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1))
      = 2 / (((J : ℝ) + 1) * Real.log 2) *
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
      (1 : ℝ) / (((J - j : ℕ) : ℝ) + 1)
      = ∑ i ∈ Finset.range (J + 1), (1 : ℝ) / ((i : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun i => (1 : ℝ) / ((i : ℝ) + 1)) (J + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjj : J + 1 - 1 - j = J - j := by omega
    rw [hjj]
  have hharm := harmonic_sum_le (J + 1)
  have hcastlog : Real.log ((J + 1 : ℕ) : ℝ) = Real.log ((J : ℝ) + 1) := by norm_cast
  calc ∑ j ∈ Finset.Ico (M + 1) (J + 1),
      1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      ≤ ∑ j ∈ Finset.Ico (M + 1) (J + 1),
        2 / (((J : ℝ) + 1) * Real.log 2) * (1 / (((J - j : ℕ) : ℝ) + 1)) := hsum1
    _ = 2 / (((J : ℝ) + 1) * Real.log 2) *
        ∑ j ∈ Finset.Ico (M + 1) (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1)) := hsum2
    _ ≤ 2 / (((J : ℝ) + 1) * Real.log 2) *
        ∑ j ∈ Finset.range (J + 1), (1 / (((J - j : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum3 hc_nonneg
    _ = 2 / (((J : ℝ) + 1) * Real.log 2) *
        ∑ i ∈ Finset.range (J + 1), (1 / ((i : ℝ) + 1)) := by rw [hreflect]
    _ ≤ 2 / (((J : ℝ) + 1) * Real.log 2) * (1 + Real.log ((J : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc_nonneg
        calc ∑ i ∈ Finset.range (J + 1), (1 : ℝ) / ((i : ℝ) + 1)
            ≤ 1 + Real.log ((J + 1 : ℕ) : ℝ) := hharm
          _ = 1 + Real.log ((J : ℝ) + 1) := by rw [hcastlog]


/-- Core of the dyadic bound, parametrized by the bracketing index J:
if 2^J ≤ x / 3 ≤ 2^(J+1), the fiberwise double sum is at most 384*x*loglog x/log x. -/
theorem sum_ratio_log_dyadic_core (x : ℝ) (p₀ J : ℕ) (hp₀ : 1 ≤ p₀)
    (hx : 9 ≤ x) (h2J3 : (2 : ℝ) ^ J ≤ x / 3)
    (hJ13 : x / 3 ≤ (2 : ℝ) ^ (J + 1)) :
    ∑ j ∈ Finset.range (J + 1),
        ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
      384 * x * Real.log (Real.log x) / Real.log x := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx2 := two_le_log x hx
  have hlogx_pos : (0 : ℝ) < Real.log x := by linarith
  have hloglog_pos : (0 : ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
  have h2J : (2 : ℝ) ^ J ≤ x := by linarith
  have hterm : ∀ j ∈ Finset.range (J + 1),
      ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
          ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ) ≤
        16 * x / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := by
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have h2j : (2 : ℝ) ^ j ≤ x / 3 := by
      calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := by
            apply pow_le_pow_right₀ (by norm_num)
            exact hj
        _ ≤ x / 3 := h2J3
    have hx2j3 : (3 : ℝ) ≤ x / (2 : ℝ) ^ j :=
      div_ge_three_of_le_third x ((2 : ℝ) ^ j) hxpos (by positivity) h2j
    have hlogj_pos : (0 : ℝ) < Real.log (x / (2 : ℝ) ^ j) := Real.log_pos (by linarith)
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [dyadic_fiber_zero_empty p₀ ⌊x / 3⌋₊ hp₀, Finset.sum_empty]
      have hden : (0 : ℝ) < (((0 : ℕ):ℝ) + 1) * Real.log (x / (2 : ℝ) ^ (0 : ℕ)) :=
        mul_pos (by positivity) hlogj_pos
      exact div_nonneg (by linarith) hden.le
    · exact le_trans (dyadic_fiber_sum_bound x p₀ j hp₀ hx h2j)
        (dyadic_term_bound x j hjpos hx h2j)
  have hsum1 := Finset.sum_le_sum hterm
  have hfactor : ∑ j ∈ Finset.range (J + 1),
      16 * x / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      = 16 * x * ∑ j ∈ Finset.range (J + 1),
          1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsplit : ∑ j ∈ Finset.range (J + 1),
      (1 : ℝ) / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      = (∑ j ∈ Finset.range (J / 2 + 1),
          (1 : ℝ) / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)))
        + ∑ j ∈ Finset.Ico (J / 2 + 1) (J + 1),
            (1 : ℝ) / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (J / 2 + 1)) (by omega)).symm
  have hlow := dyadic_low_sum x J (J / 2) hx (by omega) h2J
  have hhigh := dyadic_high_sum x J (J / 2) hx (by omega) h2J3
  have hhalf := log_x_half_le x J hx hJ13
  have hJ2 := J_le_two_log x J hx h2J
  have habs := one_add_log_le_loglog x J hx hJ2
  have hM_log : 1 + Real.log (((J / 2 : ℕ):ℝ) + 1) ≤ 4 * Real.log (Real.log x) := by
    have hle : (J / 2 : ℕ) ≤ J := Nat.div_le_self J 2
    have h1 : (((J / 2 : ℕ):ℝ) + 1) ≤ ((J : ℝ) + 1) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hle
      linarith
    have h2 : Real.log (((J / 2 : ℕ):ℝ) + 1) ≤ Real.log ((J : ℝ) + 1) :=
      Real.log_le_log (by positivity) h1
    linarith [habs]
  have hhigh_coef : 2 / (((J : ℝ) + 1) * Real.log 2) ≤ 4 / Real.log x := by
    have hlogx_ne : Real.log x ≠ 0 := hlogx_pos.ne'
    have h1 : 2 / (((J : ℝ) + 1) * Real.log 2) ≤ 2 / (Real.log x / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hhalf
    have h2 : 2 / (Real.log x / 2) = 4 / Real.log x := by
      field_simp
      try ring
    calc 2 / (((J : ℝ) + 1) * Real.log 2) ≤ 2 / (Real.log x / 2) := h1
      _ = 4 / Real.log x := h2
  have hc_low : (0 : ℝ) ≤ 2 / Real.log x := div_nonneg (by norm_num) hlogx_pos.le
  have hL2 : 2 / Real.log x * (1 + Real.log (((J / 2 : ℕ):ℝ) + 1))
      ≤ 8 * Real.log (Real.log x) / Real.log x := by
    calc 2 / Real.log x * (1 + Real.log (((J / 2 : ℕ):ℝ) + 1))
        ≤ 2 / Real.log x * (4 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_left hM_log hc_low
      _ = 8 * Real.log (Real.log x) / Real.log x := by ring
  have hH2 : 2 / (((J : ℝ) + 1) * Real.log 2) * (1 + Real.log ((J : ℝ) + 1))
      ≤ 16 * Real.log (Real.log x) / Real.log x := by
    have h1pl : (0 : ℝ) ≤ 1 + Real.log ((J : ℝ) + 1) := by
      have hln : (0 : ℝ) ≤ Real.log ((J : ℝ) + 1) :=
        Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg J))
      linarith
    calc 2 / (((J : ℝ) + 1) * Real.log 2) * (1 + Real.log ((J : ℝ) + 1))
        ≤ 4 / Real.log x * (1 + Real.log ((J : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hhigh_coef h1pl
      _ ≤ 4 / Real.log x * (4 * Real.log (Real.log x)) :=
          mul_le_mul_of_nonneg_left habs (div_nonneg (by norm_num) hlogx_pos.le)
      _ = 16 * Real.log (Real.log x) / Real.log x := by ring
  have hU : ∑ j ∈ Finset.range (J + 1),
      (1 : ℝ) / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j))
      ≤ 24 * Real.log (Real.log x) / Real.log x := by
    have h824 : 8 * Real.log (Real.log x) / Real.log x
        + 16 * Real.log (Real.log x) / Real.log x
        = 24 * Real.log (Real.log x) / Real.log x := by ring
    linarith [hsplit, hlow, hhigh, hL2, hH2, h824]
  calc ∑ j ∈ Finset.range (J + 1),
      ∑ k ∈ (Finset.Ioc p₀ ⌊x / 3⌋₊).filter (fun k => Nat.log 2 k = j),
        ((x / k) / Real.log (x / k)) * (if Nat.Prime k then 1 else 0 : ℝ)
      ≤ ∑ j ∈ Finset.range (J + 1),
        16 * x / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := hsum1
    _ = 16 * x * ∑ j ∈ Finset.range (J + 1),
        1 / (((j : ℝ) + 1) * Real.log (x / (2 : ℝ) ^ j)) := hfactor
    _ ≤ 16 * x * (24 * Real.log (Real.log x) / Real.log x) :=
        mul_le_mul_of_nonneg_left hU (by linarith)
    _ = 384 * x * Real.log (Real.log x) / Real.log x := by ring

/-- THE dyadic sum bound, now proven: the weighted prime sum
∑_(p prime ≤ x / 3) (x/p)/log(x/p) is at most 384*x*loglog x/log x. -/
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
    (hx3 : (p₀ : ℝ) ≤ x / 3) :
    (x/(p₀ : ℝ)) / Real.log (x/(p₀ : ℝ)) ≤ x / Real.log x := by
  rcases eq_or_lt_of_le hp₀ with heq | hlt
  · simp [← heq]
  · have ha : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
    have h1lt : (1 : ℝ) < (p₀ : ℝ) := by exact_mod_cast hlt
    have hconv : Convex ℝ (Set.Icc (1 : ℝ) (p₀ : ℝ)) := convex_Icc _ _
    have hint_eq : interior (Set.Icc (1 : ℝ) (p₀ : ℝ)) = Set.Ioo (1 : ℝ) (p₀ : ℝ) :=
      interior_Icc
    have hxt3_of : ∀ t, 1 ≤ t → t ≤ (p₀ : ℝ) → (3 : ℝ) ≤ x / t := by
      intro t ht1 ht2
      have htle3 : t ≤ x / 3 := le_trans ht2 hx3
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      have heq3 : x / (x / 3) = 3 := by field_simp
      have hge : x / (x / 3) ≤ x / t := by
        apply div_le_div_of_nonneg_left hxpos.le htpos htle3
      linarith [heq3 ▸ hge]
    have hcont : ContinuousOn (fun s => (x/s)/Real.log (x/s)) (Set.Icc (1 : ℝ) (p₀ : ℝ)) := by
      intro t ht
      simp only [Set.mem_Icc] at ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht.1
      have hxt3 := hxt3_of t ht.1 ht.2
      exact (differentiableAt_ratio_log x t htpos (by linarith)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun s => (x/s)/Real.log (x/s))
        (interior (Set.Icc (1 : ℝ) (p₀ : ℝ))) := by
      rw [hint_eq]
      intro t ht
      simp only [Set.mem_Ioo] at ht
      have htpos : 0 < t := lt_trans one_pos ht.1
      have hxt3 := hxt3_of t ht.1.le ht.2.le
      exact (differentiableAt_ratio_log x t htpos (by linarith)).differentiableWithinAt
    have hderiv_np : ∀ t ∈ interior (Set.Icc (1 : ℝ) (p₀ : ℝ)),
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
        have hl3 : (1 : ℝ) < Real.log 3 := by
          calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hloge1
        linarith
      have hnum_neg : (1 : ℝ) - Real.log (x/t) < 0 := by linarith
      have hden_pos : (0 : ℝ) < (Real.log (x/t))^2 := by positivity
      have hxt2_pos : (0 : ℝ) < x/t^2 := by positivity
      have hprod_neg : x/t^2 * (1 - Real.log (x/t)) < 0 := mul_neg_of_pos_of_neg hxt2_pos hnum_neg
      exact div_nonpos_of_nonpos_of_nonneg hprod_neg.le hden_pos.le
    have hanti := antitoneOn_of_deriv_nonpos hconv hcont hdiff hderiv_np
    have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (p₀ : ℝ) := ⟨le_refl _, h1lt.le⟩
    have hpmem : (p₀ : ℝ) ∈ Set.Icc (1 : ℝ) (p₀ : ℝ) := ⟨h1lt.le, le_refl _⟩
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
          (p : ℝ) ≥ 1 → x / p ≥ 3 → (piKFrom n (x / p) p : ℝ) ≤
            C * (Real.log (Real.log x)) ^ (n - 1) * ((x / p) / Real.log (x / p)) := by
        intro p hp hp1 hge3
        have h1 := hterm_bound p hp hge3
        have h2 := hloglog_crude p hp1 hge3
        have hloglogpos : 0 ≤ Real.log (Real.log (x/p)) := by
          have hxp3 : (3 : ℝ) ≤ x/p := hge3
          have he_lt3 : Real.exp 1 < 3 := by
            have := Real.exp_one_lt_d9
            linarith
          have hloge_lt3 : (1 : ℝ) < Real.log 3 := by
            calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
              _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he_lt3
          have h3le : Real.log 3 ≤ Real.log (x/p) := Real.log_le_log (by norm_num) hxp3
          have hge1 : (1 : ℝ) ≤ Real.log (x/p) := by linarith
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
        have hmge : (2 : ℝ) ^ n ≤ m := by
          have := pow_bigOmega_le m (by omega)
          rw [hmO] at this
          exact_mod_cast this
        have h4le : (4 : ℝ) ≤ 2 ^ n := by
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
        have hmle : (m : ℝ) ≤ x / p := by
          have h1 : (m : ℝ) ≤ (⌊x/p⌋₊ : ℝ) := by exact_mod_cast hm.2
          have h2 : (⌊x/p⌋₊ : ℝ) ≤ x / p := Nat.floor_le (by positivity)
          linarith
        linarith
      simp only [Nat.add_sub_cancel]
      have hxpos0 : (0 : ℝ) < x := by linarith
      have hdich : 9 ≤ x ∨ x < 9 := by
        by_cases h : (9 : ℝ) ≤ x
        · exact Or.inl h
        · exact Or.inr (not_le.mp h)
      rcases hdich with hx9 | hx9
      · -- MAIN BRANCH: x >= 9, thread through the dyadic bound
        push_cast
        classical
        have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
        have hloglog_pos : (0 : ℝ) < Real.log (Real.log x) := by
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
            have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
            unfold piKFrom
            apply Finset.card_eq_zero.mpr
            apply Finset.filter_eq_empty_iff.mpr
            intro m hm
            simp only [Finset.mem_Icc] at hm
            intro hcontra
            obtain ⟨hmO, hmin_⟩ := hcontra
            have hmprime : m.Prime := (bigOmega_eq_one_iff m).mp hmO
            have hpm : p ≤ m := hmin_ m hmprime dvd_rfl
            have hmle : (m : ℝ) ≤ x / p := by
              have h1 : (m : ℝ) ≤ (⌊x / p⌋₊ : ℝ) := by exact_mod_cast hm.2
              have h2 : (⌊x / p⌋₊ : ℝ) ≤ x / p :=
                Nat.floor_le (div_nonneg (by linarith) hppos.le)
              linarith
            have hm3 : m < 3 := by
              have hmr : (m : ℝ) < 3 := lt_of_le_of_lt hmle hlt
              exact_mod_cast hmr
            have hp2 : p = 2 := by omega
            rw [hp2] at hlt
            have h2c : ((2 : ℕ):ℝ) = 2 := by norm_num
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
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
          have hxp3 : x / (p : ℝ) < 3 := by
            have h3 : (⌊x / 3⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
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
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
          have hpleR : (p : ℝ) ≤ x / 3 := by
            have h1 : (p : ℝ) ≤ (⌊x / 3⌋₊ : ℝ) := by exact_mod_cast hple
            have h2 : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
            linarith
          have hge3 : x / (p : ℝ) ≥ 3 :=
            div_ge_three_of_le_third x (p : ℝ) (by linarith) hppos hpleR
          have hp1R : (1 : ℝ) ≤ (p : ℝ) := by
            have h2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2le
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
          have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
          have hkleR : (k : ℝ) ≤ x / 3 := by
            have h1 : (k : ℝ) ≤ (⌊x / 3⌋₊ : ℝ) := by exact_mod_cast hk.2
            have h2 : (⌊x / 3⌋₊ : ℝ) ≤ x / 3 := Nat.floor_le (by linarith)
            linarith
          have hge3 : (3 : ℝ) ≤ x / (k : ℝ) :=
            div_ge_three_of_le_third x (k : ℝ) (by linarith) hkpos hkleR
          have hlogk : (0 : ℝ) < Real.log (x / (k : ℝ)) := Real.log_pos (by linarith)
          apply mul_nonneg
          · exact div_nonneg (by linarith) hlogk.le
          · split_ifs <;> norm_num
        have hsum3 := Finset.sum_le_sum_of_subset_of_nonneg hTsub hnonneg
        have hdy := sum_ratio_log_dyadic' 1 x (le_refl 1) hx9
        have hLL_nonneg : (0 : ℝ) ≤ Real.log (Real.log x) := hloglog_pos.le
        have hCL_nonneg : (0 : ℝ) ≤ C * (Real.log (Real.log x)) ^ (n - 1) :=
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
          have hq : (0 : ℝ) ≤ x * (Real.log (Real.log x)) ^ n / Real.log x :=
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
        have hlog3_ge : (27 : ℝ)/25 ≤ Real.log 3 := by
          have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          have h1 : (23 : ℝ)/25 ≤ Real.exp (-((2 : ℝ)/25)) := by
            have := Real.add_one_le_exp (-((2 : ℝ)/25))
            linarith
          have hmul : Real.exp ((2 : ℝ)/25) * Real.exp (-((2 : ℝ)/25)) = 1 := by
            rw [← Real.exp_add]
            simp
          have h2 : Real.exp ((2 : ℝ)/25) ≤ 25 / 23 := by
            have hepos : (0 : ℝ) < Real.exp (-((2 : ℝ)/25)) := Real.exp_pos _
            nlinarith [hmul, h1, hepos, (Real.exp_pos ((2 : ℝ)/25)).le]
          have h4 : Real.exp ((27 : ℝ)/25) ≤ 3 := by
            have hsplit : Real.exp ((27 : ℝ)/25) = Real.exp 1 * Real.exp ((2 : ℝ)/25) := by
              rw [← Real.exp_add]
              norm_num
            rw [hsplit]
            nlinarith [he, h2, (Real.exp_pos ((2 : ℝ)/25)).le, (Real.exp_pos 1).le]
          have h5 : Real.log (Real.exp ((27 : ℝ)/25)) ≤ Real.log 3 :=
            Real.log_le_log (Real.exp_pos _) h4
          rwa [Real.log_exp] at h5
        have hlogx_ge : (27 : ℝ)/25 ≤ Real.log x :=
          le_trans hlog3_ge (Real.log_le_log (by norm_num) hx)
        have hlx_pos : (0 : ℝ) < Real.log x := by linarith
        have hlog3_le : Real.log 3 ≤ (9 : ℝ)/8 := by
          have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
          have h1 : (9 : ℝ)/8 ≤ Real.exp ((1 : ℝ)/8) := by
            have := Real.add_one_le_exp ((1 : ℝ)/8)
            linarith
          have h2 : (3 : ℝ) ≤ Real.exp ((9 : ℝ)/8) := by
            have hsplit : Real.exp ((9 : ℝ)/8) = Real.exp 1 * Real.exp ((1 : ℝ)/8) := by
              rw [← Real.exp_add]
              norm_num
            rw [hsplit]
            nlinarith [he, h1, (Real.exp_pos ((1 : ℝ)/8)).le, (Real.exp_pos 1).le]
          have h5 : Real.log 3 ≤ Real.log (Real.exp ((9 : ℝ)/8)) :=
            Real.log_le_log (by norm_num) h2
          rwa [Real.log_exp] at h5
        have hlogx_le : Real.log x ≤ (9 : ℝ)/4 := by
          have h1 : Real.log x ≤ Real.log 9 := Real.log_le_log (by linarith) (by linarith)
          have h2 : Real.log 9 = 2 * Real.log 3 := by
            rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
            norm_num
          linarith [hlog3_le]
        have hLL_ge : (2 : ℝ)/27 ≤ Real.log (Real.log x) := by
          have h1 : Real.log ((Real.log x)⁻¹) ≤ (Real.log x)⁻¹ - 1 :=
            Real.log_le_sub_one_of_pos (inv_pos.mpr hlx_pos)
          rw [Real.log_inv] at h1
          have h3 : 1 / Real.log x ≤ 1 / ((27 : ℝ)/25) :=
            one_div_le_one_div_of_le (by norm_num) hlogx_ge
          simp only [one_div] at h3
          have h4 : ((27 : ℝ)/25)⁻¹ = 25 / 27 := by norm_num
          rw [h4] at h3
          linarith [h1, h3]
        rcases Nat.lt_or_ge n 3 with hn3 | hn3
        · -- n <= 2: numeric absorption
          have hn2' : n ≤ 2 := by omega
          have hLLn : (4 : ℝ)/729 ≤ (Real.log (Real.log x)) ^ n := by
            calc (4 : ℝ)/729 = ((2 : ℝ)/27) ^ 2 := by norm_num
              _ ≤ ((2 : ℝ)/27) ^ n := by
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
          have hinv : (4 : ℝ)/9 ≤ 1 / Real.log x := by
            calc (4 : ℝ)/9 = 1 / ((9 : ℝ)/4) := by norm_num
              _ ≤ 1 / Real.log x := one_div_le_one_div_of_le hlx_pos hlogx_le
          have hs1 : (6000 : ℝ) ≤ (C + 1) * 2000 * x := by
            nlinarith [mul_nonneg hC.le (by linarith : (0 : ℝ) ≤ x)]
          have hs2 : (6000 : ℝ) * ((4 : ℝ)/729)
              ≤ ((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n :=
            mul_le_mul hs1 hLLn (by norm_num) (by linarith)
          have hs3 : (6000 : ℝ) * ((4 : ℝ)/729) * ((4 : ℝ)/9)
              ≤ (((C + 1) * 2000 * x) * (Real.log (Real.log x)) ^ n) * (1 / Real.log x) :=
            mul_le_mul hs2 hinv (by norm_num) (by linarith [hs2])
          calc (piKFrom (n + 1) x p₀ : ℝ)
              ≤ x := hcount
            _ ≤ 9 := by linarith
            _ ≤ (6000 : ℝ) * ((4 : ℝ)/729) * ((4 : ℝ)/9) := by norm_num
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
              calc (16 : ℕ) = 2 ^ 4 := by norm_num
                _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have hmle : (m : ℝ) ≤ x := by
              have h1 : (m : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hm.2
              have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
              linarith
            have h16r : (16 : ℝ) ≤ (m : ℝ) := by
              exact_mod_cast le_trans h16 hmge
            linarith
          rw [hzero]
          simp only [Nat.cast_zero]
          have hLLpos : (0 : ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
          apply div_nonneg _ hlx_pos.le
          apply mul_nonneg _ (pow_nonneg hLLpos.le n)
          apply mul_nonneg _ (by linarith : (0 : ℝ) ≤ x)
          nlinarith [hC]

/-- Telescoping bound: partial sums of 1/(j*sqrt j) over [2,N] never exceed 2. -/
theorem telescope_sqrt (N : ℕ) :
    ∑ j ∈ Finset.Icc 2 N, (1 : ℝ) / ((j : ℝ) * Real.sqrt j) ≤ 2 := by
  have hstep : ∀ M : ℕ,
      ∑ j ∈ Finset.Icc 2 M, (1 : ℝ) / ((j : ℝ) * Real.sqrt j)
        ≤ 2 * (1 - 1 / Real.sqrt (M : ℝ)) := by
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
        have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
        have hsM : (0 : ℝ) < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by linarith)
        have hsM1 : (0 : ℝ) < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
        have hmulM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
          Real.mul_self_sqrt (by linarith)
        have hmulM1 : Real.sqrt ((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1) = (M : ℝ) + 1 :=
          Real.mul_self_sqrt (by linarith)
        have hle : Real.sqrt (M : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) :=
          Real.sqrt_le_sqrt (by linarith)
        have hkey : (Real.sqrt ((M : ℝ) + 1) - Real.sqrt (M : ℝ)) *
            (Real.sqrt ((M : ℝ) + 1) + Real.sqrt (M : ℝ)) = 1 := by
          nlinarith [hmulM, hmulM1]
        have hcast : (((M + 1 : ℕ)):ℝ) = (M : ℝ) + 1 := by push_cast; ring
        have htail : (1 : ℝ) / (((M + 1 : ℕ):ℝ) * Real.sqrt ((M + 1 : ℕ):ℝ))
            ≤ 2 * (1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M : ℝ) + 1)) := by
          rw [hcast]
          have hdenom : (0 : ℝ) < ((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1) := by positivity
          rw [div_le_iff₀ hdenom]
          have hdiff : 1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M : ℝ) + 1)
              = (Real.sqrt ((M : ℝ) + 1) - Real.sqrt (M : ℝ)) /
                (Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) + 1)) := by
            field_simp
            try ring
          rw [hdiff]
          have hab_pos : (0 : ℝ) < Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) + 1) := by
            positivity
          have hform : 2 * ((Real.sqrt ((M : ℝ) + 1) - Real.sqrt (M : ℝ)) /
                (Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) + 1))) * (((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1))
              = (2 * (Real.sqrt ((M : ℝ) + 1) - Real.sqrt (M : ℝ)) * (((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1))) /
                (Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) + 1)) := by
            ring
          rw [hform, le_div_iff₀ hab_pos]
          nlinarith [hkey, hle, hsM, hsM1, hmulM1, hmulM,
            mul_pos hsM hsM1,
            mul_nonneg (mul_nonneg hsM1.le hsM1.le) (sub_nonneg.mpr hle),
            mul_nonneg hsM1.le (sub_nonneg.mpr hle)]
        have hfinal : 2 * (1 - 1 / Real.sqrt (M : ℝ)) +
            2 * (1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M : ℝ) + 1))
            = 2 * (1 - 1 / Real.sqrt ((M : ℝ) + 1)) := by ring
        calc ∑ j ∈ Finset.Icc 2 M, (1 : ℝ) / ((j : ℝ) * Real.sqrt j)
              + (1 : ℝ) / (((M + 1 : ℕ):ℝ) * Real.sqrt ((M + 1 : ℕ):ℝ))
            ≤ 2 * (1 - 1 / Real.sqrt (M : ℝ)) +
              2 * (1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M : ℝ) + 1)) :=
              add_le_add ih htail
          _ = 2 * (1 - 1 / Real.sqrt ((M : ℝ) + 1)) := hfinal
          _ = 2 * (1 - 1 / Real.sqrt (((M + 1 : ℕ)):ℝ)) := by rw [hcast]
  calc ∑ j ∈ Finset.Icc 2 N, (1 : ℝ) / ((j : ℝ) * Real.sqrt j)
      ≤ 2 * (1 - 1 / Real.sqrt (N : ℝ)) := hstep N
    _ ≤ 2 := by
        have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (N : ℝ) := by positivity
        linarith

/-- Power-of-log bound: (log y)^m ≤ (2m)^m * sqrt y for y >= 1, m >= 1. -/
theorem log_pow_le_sqrt (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 1 ≤ y) :
    (Real.log y) ^ m ≤ (2 * (m : ℝ)) ^ m * Real.sqrt y := by
  have hypos : (0 : ℝ) < y := by linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have h1 : Real.log (y ^ ((1 : ℝ) / (2 * (m : ℝ)))) = (1 / (2 * (m : ℝ))) * Real.log y :=
    Real.log_rpow hypos _
  have h2 : Real.log (y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ≤ y ^ ((1 : ℝ) / (2 * (m : ℝ))) :=
    Real.log_le_self (Real.rpow_nonneg hypos.le _)
  have h3 : (1 / (2 * (m : ℝ))) * Real.log y ≤ y ^ ((1 : ℝ) / (2 * (m : ℝ))) := by
    rw [← h1]
    exact h2
  have hlog_le : Real.log y ≤ 2 * (m : ℝ) * y ^ ((1 : ℝ) / (2 * (m : ℝ))) := by
    calc Real.log y = 2 * (m : ℝ) * ((1 / (2 * (m : ℝ))) * Real.log y) := by
          field_simp
      _ ≤ 2 * (m : ℝ) * y ^ ((1 : ℝ) / (2 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hlog_nn : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hp : (Real.log y) ^ m ≤ (2 * (m : ℝ) * y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ m := by
    apply pow_le_pow_left₀ hlog_nn hlog_le
  have hsplit : (2 * (m : ℝ) * y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ m
      = (2 * (m : ℝ)) ^ m * (y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ m := mul_pow _ _ _
  have hrpow : (y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ m = Real.sqrt y := by
    rw [← Real.rpow_natCast (y ^ ((1 : ℝ) / (2 * (m : ℝ)))) m,
      ← Real.rpow_mul hypos.le]
    rw [show (1 : ℝ) / (2 * (m : ℝ)) * (m : ℝ) = 1 / 2 by field_simp; try ring]
    rw [Real.sqrt_eq_rpow]
  calc (Real.log y) ^ m ≤ (2 * (m : ℝ) * y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ m := hp
    _ = (2 * (m : ℝ)) ^ m * (y ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ m := hsplit
    _ = (2 * (m : ℝ)) ^ m * Real.sqrt y := by rw [hrpow]

/-- The summand 1/(t log t) is antitone past 2. -/
theorem inv_mul_log_le (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    1 / (b * Real.log b) ≤ 1 / (a * Real.log a) := by
  have hla : (0 : ℝ) < Real.log a := Real.log_pos (by linarith)
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpa : (0 : ℝ) < a * Real.log a := mul_pos (by linarith) hla
  apply one_div_le_one_div_of_le hpa
  apply mul_le_mul hab hlb hla.le (by linarith)

/-- Nonzero terms in dyadic block j inject into the piK count at 2^(j+1). -/
theorem block_count_le_piK (kk j M : ℕ) :
    (((Finset.Ioc 1 M).filter (fun n => Nat.log 2 n = j)).filter
        (fun n => 2 ≤ n ∧ bigOmega n = kk)).card
      ≤ piK kk (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) := by
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
    C * (2 : ℝ) ^ (j + 1) * (Real.log (Real.log ((2 : ℝ) ^ (j + 1)))) ^ m /
        Real.log ((2 : ℝ) ^ (j + 1)) * (1 / ((2 : ℝ) ^ j * Real.log ((2 : ℝ) ^ j)))
      ≤ 4 * C * (2 * (m : ℝ)) ^ m / (Real.log 2) ^ 2 * (1 / ((j : ℝ) * Real.sqrt j)) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2h : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hsq : Real.exp ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have he := Real.exp_one_lt_d9
    have hp := Real.exp_pos ((1 : ℝ) / 2)
    have h2 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by nlinarith
    have h2' : Real.log (Real.exp ((1 : ℝ) / 2)) ≤ Real.log 2 :=
      Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h2'
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hsj : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.mpr hjpos
  have hjj : Real.sqrt j * Real.sqrt j = (j : ℝ) := Real.mul_self_sqrt hjpos.le
  have hA : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hlogj : Real.log ((2 : ℝ) ^ j) = (j : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogj1 : Real.log ((2 : ℝ) ^ (j + 1)) = ((j : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogj, hlogj1]
  have hll_ub : Real.log (((j : ℝ) + 1) * Real.log 2) ≤ Real.log ((j : ℝ) + 1) := by
    apply Real.log_le_log (mul_pos hj1pos hl2)
    nlinarith [hl2', hj1pos]
  have hll_nn : (0 : ℝ) ≤ Real.log (((j : ℝ) + 1) * Real.log 2) := by
    apply Real.log_nonneg
    nlinarith [hl2h, hjR, mul_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - 1) hl2.le]
  have hpow1 : (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m ≤ (Real.log ((j : ℝ) + 1)) ^ m := by
    apply pow_le_pow_left₀ hll_nn hll_ub
  have hLP : (Real.log ((j : ℝ) + 1)) ^ m ≤ (2 * (m : ℝ)) ^ m * Real.sqrt ((j : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · subst hm0
      simp only [pow_zero, one_mul]
      have h1 : Real.sqrt 1 ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_one] at h1
      linarith
    · exact log_pow_le_sqrt m hm1 ((j : ℝ) + 1) (by linarith)
  have hsq1 : Real.sqrt ((j : ℝ) + 1) ≤ 2 * Real.sqrt j := by
    have h4 : Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt (4 * (j : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h5 : Real.sqrt (4 * (j : ℝ)) = 2 * Real.sqrt j := by
      rw [show (4 : ℝ) * (j : ℝ) = (2 : ℝ) ^ 2 * (j : ℝ) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h5] at h4
    exact h4
  have hX : (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m
      ≤ (2 * (m : ℝ)) ^ m * (2 * Real.sqrt j) := by
    have h3 : (2 * (m : ℝ)) ^ m * Real.sqrt ((j : ℝ) + 1)
        ≤ (2 * (m : ℝ)) ^ m * (2 * Real.sqrt j) :=
      mul_le_mul_of_nonneg_left hsq1 (pow_nonneg (by positivity) m)
    linarith [hpow1, hLP, h3]
  have hE1 : C * (2 : ℝ) ^ (j + 1) * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m /
        (((j : ℝ) + 1) * Real.log 2) * (1 / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)))
      = 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m /
        (((j : ℝ) + 1) * (j : ℝ) * (Real.log 2) ^ 2) := by
    rw [pow_succ]
    field_simp
    try ring
  have hEL : 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m /
        (((j : ℝ) + 1) * (j : ℝ) * (Real.log 2) ^ 2)
      = 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j : ℝ) + 1) * (j : ℝ))) * (1 / (Real.log 2) ^ 2) := by
    field_simp [hl2.ne', hjpos.ne', hj1pos.ne']
    try ring
  have hinv : 1 / (((j : ℝ) + 1) * (j : ℝ)) ≤ 1 / ((j : ℝ) * (j : ℝ)) := by
    apply one_div_le_one_div_of_le (mul_pos hjpos hjpos)
    nlinarith [hjpos]
  have hK0 : (0 : ℝ) ≤ 2 * C * ((2 * (m : ℝ)) ^ m * (2 * Real.sqrt j)) := by
    apply mul_nonneg (by linarith)
    apply mul_nonneg (pow_nonneg (by positivity) m)
    positivity
  have hstep1 : 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m
      ≤ 2 * C * ((2 * (m : ℝ)) ^ m * (2 * Real.sqrt j)) :=
    mul_le_mul_of_nonneg_left hX (by linarith)
  have hstep2 : 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j : ℝ) + 1) * (j : ℝ)))
      ≤ 2 * C * ((2 * (m : ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j : ℝ) * (j : ℝ))) :=
    mul_le_mul hstep1 hinv (le_of_lt (one_div_pos.mpr (mul_pos hj1pos hjpos))) hK0
  have hstep3 : 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j : ℝ) + 1) * (j : ℝ))) * (1 / (Real.log 2) ^ 2)
      ≤ 2 * C * ((2 * (m : ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j : ℝ) * (j : ℝ))) *
        (1 / (Real.log 2) ^ 2) :=
    mul_le_mul_of_nonneg_right hstep2 (le_of_lt (one_div_pos.mpr (pow_pos hl2 2)))
  have hER : 2 * C * ((2 * (m : ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j : ℝ) * (j : ℝ))) *
        (1 / (Real.log 2) ^ 2)
      = 4 * C * (2 * (m : ℝ)) ^ m / (Real.log 2) ^ 2 * (Real.sqrt j / ((j : ℝ) * (j : ℝ))) := by
    ring
  have hfrac : Real.sqrt j / ((j : ℝ) * (j : ℝ)) = 1 / ((j : ℝ) * Real.sqrt j) := by
    rw [div_eq_div_iff (mul_pos hjpos hjpos).ne' (mul_pos hjpos hsj).ne']
    linear_combination (j : ℝ) * hjj
  calc C * (2 : ℝ) ^ (j + 1) * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m /
        (((j : ℝ) + 1) * Real.log 2) * (1 / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)))
      = 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m /
        (((j : ℝ) + 1) * (j : ℝ) * (Real.log 2) ^ 2) := hE1
    _ = 2 * C * (Real.log (((j : ℝ) + 1) * Real.log 2)) ^ m *
        (1 / (((j : ℝ) + 1) * (j : ℝ))) * (1 / (Real.log 2) ^ 2) := hEL
    _ ≤ 2 * C * ((2 * (m : ℝ)) ^ m * (2 * Real.sqrt j)) * (1 / ((j : ℝ) * (j : ℝ))) *
        (1 / (Real.log 2) ^ 2) := hstep3
    _ = 4 * C * (2 * (m : ℝ)) ^ m / (Real.log 2) ^ 2 *
        (Real.sqrt j / ((j : ℝ) * (j : ℝ))) := hER
    _ = 4 * C * (2 * (m : ℝ)) ^ m / (Real.log 2) ^ 2 * (1 / ((j : ℝ) * Real.sqrt j)) := by
        rw [hfrac]

/-- Manuscript Definition 2.3: S(m) = sum_{j+l=m} int_1^2 (-log(s-1))^l/l! * 2^(-js) ds.
Indexed by j in range (m+1), with l = m - j. -/
noncomputable def Sm (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ∫ s in Set.Ioc (1 : ℝ) 2,
      (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (2 : ℝ) ^ (-(j : ℝ) * s)
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
      (-Real.log (s - 1)) ^ (0 - 0) / (Nat.factorial (0 - 0)) * (2 : ℝ) ^ (-((0 : ℕ):ℝ) * s)
        = 1 := by
    intro s
    norm_num
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s _ => hintegrand s)]
  rw [MeasureTheory.setIntegral_const]
  have hvol : MeasureTheory.volume.real (Set.Ioc (1 : ℝ) 2) = 1 := by
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
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ i = (Nat.factorial i : ℝ) := by
  calc ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ i
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (((i : ℝ) + 1) - 1) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [show ((i : ℝ) + 1) - 1 = (i : ℝ) by ring, Real.rpow_natCast]
    _ = Real.Gamma ((i : ℝ) + 1) := (Real.Gamma_eq_integral (by positivity)).symm
    _ = (Nat.factorial i : ℝ) := Real.Gamma_nat_eq_factorial i

/-- Manuscript eq (5): J(i) for block m, as an integral over u > 0. -/
noncomputable def Jint (m i : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-((m - i : ℕ):ℝ) * Real.exp (-u))

/-- Anchor: J(0) at m = 0 is 1 (the integrand collapses to e^(-u)). -/
theorem Jint_zero : Jint 0 0 = 1 := by
  unfold Jint
  have hcong : ∀ u : ℝ,
      u ^ 0 * Real.exp (-u) * (2 : ℝ) ^ (-(((0 : ℕ) - 0 : ℕ):ℝ) * Real.exp (-u))
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
    ∫ s in Set.Ioc (1 : ℝ) 2, g s
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * g (1 + Real.exp (-u)) := by
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
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

/-- Integrability on (1,2] transfers from (0,infty) through the substitution
s = 1 + e^(-u), by the integrability companion to integral_Ioc_subst.
This is what makes Sm (and hence Am, deltaM, Theorem 4.1) statements about a
genuine integral rather than about Lean's junk value for a non-integrable one. -/
theorem integrableOn_Ioc_subst (g : ℝ → ℝ)
    (hg : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp (-u) * g (1 + Real.exp (-u))) (Set.Ioi (0 : ℝ))) :
    MeasureTheory.IntegrableOn g (Set.Ioc (1 : ℝ) 2) := by
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => 1 + Real.exp (-u))
        (Real.exp (-u) * (-1)) (Set.Ioi 0) u := by
    intro u _
    exact (((hasDerivAt_neg u).exp).const_add 1).hasDerivWithinAt
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv subst_injOn g
  rw [subst_image] at hiff
  have hIoo : MeasureTheory.IntegrableOn g (Set.Ioo (1 : ℝ) 2) := by
    rw [hiff]
    apply hg.congr_fun _ measurableSet_Ioi
    intro u _
    simp only [smul_eq_mul, mul_neg_one, abs_neg, abs_of_pos (Real.exp_pos _)]
  exact hIoo.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm

/-- Manuscript eq (5): A_m = sum_{i <= m} 2^i / i! * J(i), by the substitution
s = 1 + e^(-u) applied termwise and reflecting the sum index. -/
theorem Am_eq_sum_Jint (m : ℕ) :
    Am m = ∑ i ∈ Finset.range (m + 1),
      (2 : ℝ) ^ i / (Nat.factorial i) * Jint m i := by
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (2 : ℝ) ^ m * ∫ s in Set.Ioc (1 : ℝ) 2,
          (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (2 : ℝ) ^ (-(j : ℝ) * s)
        = (2 : ℝ) ^ (m - j) / (Nat.factorial (m - j)) * Jint m (m - j) := by
    intro j hjm
    have hj : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjm)
    have h2mj : (2 : ℝ) ^ (m : ℕ) * (2 : ℝ) ^ (-(j : ℝ)) = (2 : ℝ) ^ ((m - j : ℕ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_natCast (2 : ℝ) (m - j),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), Nat.cast_sub hj]
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
    rw [show -(j : ℝ) * (1 + Real.exp (-u)) = -(j : ℝ) + -(j : ℝ) * Real.exp (-u) by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    field_simp
    rw [← h2mj]
    ring
  calc Am m = ∑ j ∈ Finset.range (m + 1),
        (2 : ℝ) ^ m * ∫ s in Set.Ioc (1 : ℝ) 2,
          (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (2 : ℝ) ^ (-(j : ℝ) * s) := by
        unfold Am Sm
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (m + 1),
        (2 : ℝ) ^ (m - j) / (Nat.factorial (m - j)) * Jint m (m - j) :=
        Finset.sum_congr rfl hterm
    _ = ∑ i ∈ Finset.range (m + 1),
        (2 : ℝ) ^ i / (Nat.factorial i) * Jint m i := by
        exact Finset.sum_range_reflect (fun i => (2 : ℝ) ^ i / (Nat.factorial i) * Jint m i) (m + 1)

/-- Manuscript Thm 4.1: B_j(u) = 2^(-j e^(-u)) - 1 + j log 2 e^(-u), the
convexity gap driving identity (11). -/
noncomputable def Bfun (j : ℕ) (u : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(j : ℝ) * Real.exp (-u)) - 1 + (j : ℝ) * Real.log 2 * Real.exp (-u)

/-- B_j(u) >= 0: from e^x >= 1 + x at x = -(j log 2) e^(-u). -/
theorem Bfun_nonneg (j : ℕ) (u : ℝ) : 0 ≤ Bfun j u := by
  unfold Bfun
  have hrw : (2 : ℝ) ^ (-(j : ℝ) * Real.exp (-u))
      = Real.exp (-(j : ℝ) * Real.exp (-u) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hrw]
  have h := Real.add_one_le_exp (-(j : ℝ) * Real.exp (-u) * Real.log 2)
  nlinarith [h]

/-- Manuscript (11): beta-circle, the nonnegative integral coefficient. -/
noncomputable def betaCirc (i j : ℕ) : ℝ :=
  (1 / (Nat.factorial i : ℝ)) *
    ∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-u) * Bfun j u

/-- The scaled Gamma evaluation: int_{u>0} u^i e^(-2u) du = i! / 2^(i+1),
via the linear substitution u = v / 2. -/
theorem integral_pow_exp_neg_two_mul (i : ℕ) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-(2 * u))
      = (Nat.factorial i : ℝ) / 2 ^ (i + 1) := by
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
    (fun v => v ^ i * Real.exp (-v)) (0 : ℝ) (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero] at hcomp
  have hcong : ∀ u ∈ Set.Ioi (0 : ℝ),
      u ^ i * Real.exp (-(2 * u)) = ((2 * u) ^ i * Real.exp (-(2 * u))) / 2 ^ i := by
    intro u _
    rw [mul_pow]
    field_simp
    try ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcong]
  rw [MeasureTheory.integral_div]
  rw [show (∫ u in Set.Ioi (0 : ℝ), (2 * u) ^ i * Real.exp (-(2 * u)))
      = ∫ u in Set.Ioi (0 : ℝ), (fun v => v ^ i * Real.exp (-v)) (2 * u) from rfl]
  rw [hcomp]
  have hbase : ∫ v in Set.Ioi (0 : ℝ), v ^ i * Real.exp (-v)
      = (Nat.factorial i : ℝ) := by
    rw [← integral_exp_neg_mul_pow i]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    simp only
    ring
  rw [smul_eq_mul, hbase]
  rw [show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num]
  field_simp
  try ring

/-- The scaled Gamma evaluation at 3: int_{u>0} u^i e^(-3u) du = i!/3^(i+1).
Needed for Theorem 6.1's remainder bound, where the (s-1)^2 weight produces
e^(-3t) under the substitution s = 1 + e^(-t). -/
theorem integral_pow_exp_neg_three_mul (i : ℕ) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-(3 * u))
      = (Nat.factorial i : ℝ) / 3 ^ (i + 1) := by
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi
    (fun v => v ^ i * Real.exp (-v)) (0 : ℝ) (by norm_num : (0 : ℝ) < 3)
  simp only [mul_zero] at hcomp
  have hcong : ∀ u ∈ Set.Ioi (0 : ℝ),
      u ^ i * Real.exp (-(3 * u)) = ((3 * u) ^ i * Real.exp (-(3 * u))) / 3 ^ i := by
    intro u _
    rw [mul_pow]
    field_simp
    try ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcong]
  rw [MeasureTheory.integral_div, hcomp]
  rw [show (∫ x in Set.Ioi (0 : ℝ), x ^ i * Real.exp (-x))
      = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ i by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring]
  rw [integral_exp_neg_mul_pow i]
  simp only [smul_eq_mul]
  rw [pow_succ]
  field_simp

/-- The (s-1)^2-weighted integral: int_1^2 (-log(s-1))^l/l! (s-1)^2 ds
= 3^(-l-1).  Under s = 1 + e^(-t) it becomes int_0^inf t^l/l! e^(-3t) dt.
This is Theorem 6.1's remainder integral; the manuscript's factor 1 / 2 comes
from the Taylor remainder (s-1)^2 / 2, not from here.
Verified numerically at l = 0, 1, 3. -/
theorem integral_log_pow_sub_one_sq (l : ℕ) :
    (∫ s in Set.Ioc (1 : ℝ) 2,
      (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) ^ 2)
      = 1 / (3 : ℝ) ^ (l + 1) := by
  rw [integral_Ioc_subst (fun s : ℝ =>
    (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) ^ 2)]
  have hsimp : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
      Real.exp (-u) * ((-Real.log ((1 + Real.exp (-u)) - 1)) ^ l / (Nat.factorial l)
          * ((1 + Real.exp (-u)) - 1) ^ 2)
        = ((Nat.factorial l : ℝ))⁻¹ * (u ^ l * Real.exp (-(3 * u))) := by
    intro u _
    simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
    rw [show Real.exp (-(3 * u)) = Real.exp (-u) * (Real.exp (-u) * Real.exp (-u)) by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf]
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsimp]
  rw [MeasureTheory.integral_const_mul, integral_pow_exp_neg_three_mul]
  have hfac : ((Nat.factorial l : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  field_simp

/-- The series that makes Theorem 6.1's Gamma k-independent:
sum_{l>=0} 2^l 3^(-l-1) = 1 exactly.
This is why the l-sum in the remainder bound does not grow with k. -/
theorem geom_two_three : HasSum (fun l : ℕ => (2 : ℝ) ^ l * (1 / (3 : ℝ) ^ (l + 1))) 1 := by
  have hgeom : HasSum (fun l : ℕ => ((2 : ℝ)/3) ^ l) (1 - (2 : ℝ)/3)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hval : ((1 : ℝ) - 2 / 3)⁻¹ = 3 := by norm_num
  rw [hval] at hgeom
  have h3 := hgeom.mul_left ((1 : ℝ)/3)
  have hone : (1 : ℝ)/3 * 3 = 1 := by norm_num
  rw [hone] at h3
  apply h3.congr_fun
  intro l
  rw [div_pow]
  field_simp
  ring

/-- Partial sums of the geometric series are at most its total, 1. -/
theorem geom_partial_le (m : ℕ) :
    ∑ l ∈ Finset.range (m + 1), (2 : ℝ) ^ l * (1 / (3 : ℝ) ^ (l + 1)) ≤ 1 := by
  apply sum_le_hasSum _ _ geom_two_three
  intro l _
  positivity

/-- The remainder inner sum is at most 2^i.
Reflecting j -> l = (k-i) - j turns 2^k 2^(-j) 3^(-(k-i-j)-1) into
2^i * 2^l 3^(-l-1), and the partial geometric sum is at most 1. -/
theorem remainder_inner_le (k i : ℕ) (hik : i ≤ k) :
    ∑ j ∈ Finset.range (k - i + 1),
        (2 : ℝ) ^ k * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))
      ≤ (2 : ℝ) ^ i := by
  have hrefl := Finset.sum_range_reflect
    (fun j => (2 : ℝ) ^ k * ((2 : ℝ) ^ (-(j : ℝ))
      * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))) (k - i + 1)
  rw [← hrefl]
  have hterm : ∀ l ∈ Finset.range (k - i + 1),
      (2 : ℝ) ^ k * ((2 : ℝ) ^ (-((k - i + 1 - 1 - l : ℕ) : ℝ))
        * (1 / (3 : ℝ) ^ ((k - i - (k - i + 1 - 1 - l)) + 1)))
      = (2 : ℝ) ^ i * ((2 : ℝ) ^ l * (1 / (3 : ℝ) ^ (l + 1))) := by
    intro l hl
    have hlk : l ≤ k - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hidx : k - i + 1 - 1 - l = k - i - l := by omega
    rw [hidx]
    have hidx2 : k - i - (k - i - l) = l := by omega
    rw [hidx2]
    have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ (-((k - i - l : ℕ) : ℝ))
        = (2 : ℝ) ^ i * (2 : ℝ) ^ l := by
      rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast (2 : ℝ) i,
        ← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      have : ((k - i - l : ℕ) : ℝ) = (k : ℝ) - (i : ℝ) - (l : ℝ) := by
        rw [Nat.cast_sub (by omega : l ≤ k - i), Nat.cast_sub hik]
      rw [this]
      ring
    calc (2 : ℝ) ^ k * ((2 : ℝ) ^ (-((k - i - l : ℕ) : ℝ))
          * (1 / (3 : ℝ) ^ (l + 1)))
        = ((2 : ℝ) ^ k * (2 : ℝ) ^ (-((k - i - l : ℕ) : ℝ)))
          * (1 / (3 : ℝ) ^ (l + 1)) := by ring
      _ = ((2 : ℝ) ^ i * (2 : ℝ) ^ l) * (1 / (3 : ℝ) ^ (l + 1)) := by rw [hpow]
      _ = (2 : ℝ) ^ i * ((2 : ℝ) ^ l * (1 / (3 : ℝ) ^ (l + 1))) := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeom := geom_partial_le (k - i)
  have h2i : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
  nlinarith [hgeom, h2i]

/-- Integrability of the Gamma integrand u^i e^(-u) on (0, infty). -/
theorem integrable_pow_exp (i : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ i * Real.exp (-u)) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
  apply h.congr_fun ?_ measurableSet_Ioi
  intro u hu
  simp only
  rw [show ((i : ℝ) + 1) - 1 = (i : ℝ) by ring, Real.rpow_natCast]
  ring

/-- Integrability of u^i e^(-2u) on (0, infty), by domination. -/
theorem integrable_pow_exp_two (i : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ i * Real.exp (-(2 * u))) (Set.Ioi 0) := by
  apply MeasureTheory.Integrable.mono (integrable_pow_exp i)
    (by fun_prop : Continuous fun u : ℝ => u ^ i * Real.exp (-(2 * u))).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := Set.mem_Ioi.mp hu
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le),
    abs_of_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu0.le i)
  apply Real.exp_le_exp.mpr
  linarith

/-- Integrability of u^i e^(-3u) on (0, infty), by comparison with the
exponent-2 version: e^(-3u) <= e^(-2u) for u > 0. -/
theorem integrable_pow_exp_three (i : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ i * Real.exp (-(3 * u)))
      (Set.Ioi (0 : ℝ)) := by
  apply MeasureTheory.Integrable.mono (integrable_pow_exp_two i)
  · apply Continuous.aestronglyMeasurable
    exact (continuous_pow i).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have hexp : Real.exp (-(3 * u)) ≤ Real.exp (-(2 * u)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hpow : (0 : ℝ) ≤ u ^ i := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ i * Real.exp (-(3 * u))),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ i * Real.exp (-(2 * u)))]
    exact mul_le_mul_of_nonneg_left hexp hpow

/-- Integrability of the (s-1)^2-weighted integrand on (1,2]. -/
theorem integrable_log_pow_sub_one_sq (l : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) ^ 2)
      (Set.Ioc (1 : ℝ) 2) := by
  apply integrableOn_Ioc_subst
  have hconst := (integrable_pow_exp_three l).const_mul (((Nat.factorial l : ℝ))⁻¹)
  apply MeasureTheory.IntegrableOn.congr_fun hconst _ measurableSet_Ioi
  intro u hu
  simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
  rw [show Real.exp (-(3 * u)) = Real.exp (-u) * (Real.exp (-u) * Real.exp (-u)) by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf]
  field_simp

/-- Per-term remainder bound: the Taylor remainder integrates to at most
gh_i / 2 * 2^(-j) * 3^(-l-1).  Mirrors S2_term_le with the (s-1)^2 weight. -/
theorem Dk_remainder_term_le (j l : ℕ) (gh_i : ℝ) (hgh0 : 0 ≤ gh_i) :
    (∫ s in Set.Ioc (1 : ℝ) 2,
      gh_i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))))
      ≤ gh_i / 2 * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ (l + 1))) := by
  have hL : ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) ^ 2 := by
    intro s hs
    apply mul_nonneg _ (by positivity)
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
  have hright := ((integrable_log_pow_sub_one_sq l).const_mul
    (gh_i / 2 * (2 : ℝ) ^ (-(j : ℝ))))
  have hmono : (∫ s in Set.Ioc (1 : ℝ) 2,
        gh_i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))))
      ≤ ∫ s in Set.Ioc (1 : ℝ) 2,
        (gh_i / 2 * (2 : ℝ) ^ (-(j : ℝ)))
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hright ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
      have hLl : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
        apply div_nonneg _ (by positivity)
        apply pow_nonneg
        simp only [neg_nonneg]
        exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
      simp only [Pi.zero_apply]
      apply mul_nonneg
      · apply div_nonneg _ (by norm_num)
        exact mul_nonneg hgh0 (sq_nonneg _)
      · exact mul_nonneg (le_of_lt h2) hLl
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hmonoexp : (2 : ℝ) ^ (-(j : ℝ) * s) ≤ (2 : ℝ) ^ (-(j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        nlinarith [hs.1]
      have hLs := hL s hs
      have hLl : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
        apply div_nonneg _ (by positivity)
        apply pow_nonneg
        simp only [neg_nonneg]
        exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
      have hsq : (0 : ℝ) ≤ (s - 1) ^ 2 := sq_nonneg _
      calc gh_i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
          ≤ gh_i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ))
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hmonoexp hLl
        _ = (gh_i / 2 * (2 : ℝ) ^ (-(j : ℝ)))
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) ^ 2) := by ring
  rw [MeasureTheory.integral_const_mul, integral_log_pow_sub_one_sq] at hmono
  calc (∫ s in Set.Ioc (1 : ℝ) 2,
        gh_i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))))
      ≤ (gh_i / 2 * (2 : ℝ) ^ (-(j : ℝ))) * (1 / (3 : ℝ) ^ (l + 1)) := hmono
    _ = gh_i / 2 * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ (l + 1))) := by ring

/-- Integrability of the J-integrand: the damping factor is at most 1. -/
theorem integrable_Jint_integrand (c : ℝ) (hc : 0 ≤ c) (i : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-c * Real.exp (-u)))
      (Set.Ioi 0) := by
  have hfeq : (fun u : ℝ => u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-c * Real.exp (-u)))
      = fun u : ℝ => u ^ i * Real.exp (-u) * Real.exp (-c * Real.exp (-u) * Real.log 2) := by
    funext u
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hfeq]
  apply MeasureTheory.Integrable.mono (integrable_pow_exp i)
    (by fun_prop :
      Continuous fun u : ℝ => u ^ i * Real.exp (-u) * Real.exp (-c * Real.exp (-u) * Real.log 2)).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := Set.mem_Ioi.mp hu
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -c * Real.exp (-u) * Real.log 2 ≤ 0 := by
    have h1 : (0 : ℝ) ≤ c * Real.exp (-u) * Real.log 2 :=
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

/-- Sm's integrand is integrable on (1,2].
Transfers from integrable_Jint_integrand through integrableOn_Ioc_subst.
Without this, Sm would be Lean's junk value for a non-integrable integral, and
Am, deltaM and Theorem 4.1 would all be vacuous. -/
theorem integrable_Sm_integrand (l j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (2 : ℝ) ^ (-(j : ℝ) * s))
      (Set.Ioc (1 : ℝ) 2) := by
  apply integrableOn_Ioc_subst
  have hJ := integrable_Jint_integrand (j : ℝ) (by positivity) l
  have hconst := hJ.const_mul (((Nat.factorial l : ℝ))⁻¹ * (2 : ℝ) ^ (-(j : ℝ)))
  apply MeasureTheory.IntegrableOn.congr_fun hconst _ measurableSet_Ioi
  intro u hu
  have hexp : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
  rw [show (-(j : ℝ)) * (1 + Real.exp (-u)) = -(j : ℝ) + -(j : ℝ) * Real.exp (-u) by ring]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  field_simp

/-- The J-split (manuscript Thm 4.1 engine): J(i) decomposes exactly into the
Bfun piece, the Gamma piece, and the log2-weighted scaled piece. -/
theorem Jint_split (m i : ℕ) :
    Jint m i = (Nat.factorial i : ℝ) * betaCirc i (m - i)
      + (Nat.factorial i : ℝ)
      - ((m - i : ℕ) : ℝ) * Real.log 2 * ((Nat.factorial i : ℝ) / 2 ^ (i + 1)) := by
  have hfacne : ((Nat.factorial i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hpt : ∀ u : ℝ,
      u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-(((m - i : ℕ)):ℝ) * Real.exp (-u))
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
          (u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-(((m - i : ℕ)):ℝ) * Real.exp (-u))
            - u ^ i * Real.exp (-u))
          + ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))) := by
      funext u
      have h := hpt u
      linarith [h]
    rw [hfeq]
    exact (hI3.sub hI1).add (hI2.const_mul _)
  have hbase : ∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-u)
      = (Nat.factorial i : ℝ) := by
    rw [← integral_exp_neg_mul_pow i]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only
    ring
  have hbeta : ∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-u) * Bfun (m - i) u
      = (Nat.factorial i : ℝ) * betaCirc i (m - i) := by
    unfold betaCirc
    field_simp
  unfold Jint
  calc ∫ u in Set.Ioi (0 : ℝ),
        u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-(((m - i : ℕ)):ℝ) * Real.exp (-u))
      = ∫ u in Set.Ioi (0 : ℝ),
        (u ^ i * Real.exp (-u) * Bfun (m - i) u + u ^ i * Real.exp (-u)
          - ((m - i : ℕ) : ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u)))) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [hpt u]
    _ = (∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-u) * Bfun (m - i) u)
        + (∫ u in Set.Ioi (0 : ℝ), u ^ i * Real.exp (-u))
        - ∫ u in Set.Ioi (0 : ℝ),
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
      + ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i (m - i) := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (2 : ℝ) ^ i / (Nat.factorial i) * Jint m i
        = (2 : ℝ) ^ i * betaCirc i (m - i) + (2 : ℝ) ^ i
          - ((m - i : ℕ) : ℝ) * Real.log 2 / 2 := by
    intro i _
    rw [Jint_split m i]
    have hfacne : ((Nat.factorial i : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have h2 : (2 : ℝ) ^ (i + 1) = 2 ^ i * 2 := by ring
    field_simp [h2]
    ring
  have hsum : ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i / (Nat.factorial i) * Jint m i
      = (∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i (m - i))
        + (∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i)
        - (∑ i ∈ Finset.range (m + 1), ((m - i : ℕ) : ℝ) * Real.log 2 / 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have hgeom : ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i = 2 ^ (m + 1) - 1 := by
    have := geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) (m + 1)
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
    have hu0 : (0 : ℝ) < u := Set.mem_Ioi.mp hu
    apply mul_nonneg (mul_nonneg (pow_nonneg hu0.le i) (Real.exp_pos _).le)
    exact Bfun_nonneg j u

/-- MANUSCRIPT THEOREM 4.1, LOWER BOUND: delta_m >= -1 - (log 2 / 4) m,
for every m. Immediate from identity (11) and nonnegativity of beta-circle. -/
theorem deltaM_lower_bound (m : ℕ) :
    -1 - (Real.log 2 / 4) * (m : ℝ) ≤ deltaM m := by
  rw [deltaM_identity m]
  have hsum : (0 : ℝ) ≤
      ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i (m - i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by positivity) (betaCirc_nonneg i (m - i))
  linarith

/-- Manuscript Thm 4.1: B_j is increasing in j (the 2^(-j e^-u) factor shrinks
faster than the linear term grows). Stated as the comparison needed there. -/
theorem Bfun_mono (j m : ℕ) (hjm : j ≤ m) (u : ℝ) :
    Bfun j u ≤ Bfun m u := by
  unfold Bfun
  have hE : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hjR : ((j : ℕ):ℝ) ≤ ((m : ℕ):ℝ) := by exact_mod_cast hjm
  have hgap : (2 : ℝ) ^ (-((m : ℕ):ℝ) * Real.exp (-u))
      - (2 : ℝ) ^ (-((j : ℕ):ℝ) * Real.exp (-u))
      + (((m : ℕ):ℝ) - ((j : ℕ):ℝ)) * Real.log 2 * Real.exp (-u) ≥ 0 := by
    set c := ((m : ℕ):ℝ) - ((j : ℕ):ℝ) with hc
    have hc0 : (0 : ℝ) ≤ c := by rw [hc]; linarith
    have hrw1 : (2 : ℝ) ^ (-((m : ℕ):ℝ) * Real.exp (-u))
        = (2 : ℝ) ^ (-((j : ℕ):ℝ) * Real.exp (-u)) *
          (2 : ℝ) ^ (-c * Real.exp (-u)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [hc]
      ring
    have hbase : (0 : ℝ) < (2 : ℝ) ^ (-((j : ℕ):ℝ) * Real.exp (-u)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hbase_le : (2 : ℝ) ^ (-((j : ℕ):ℝ) * Real.exp (-u)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (0 : ℝ) ≤ ((j : ℕ):ℝ) * Real.exp (-u) :=
        mul_nonneg (Nat.cast_nonneg j) hE.le
      linarith
    have hB := Bfun_nonneg 0 u
    have hkey : (1 : ℝ) - (2 : ℝ) ^ (-c * Real.exp (-u))
        ≤ c * Real.log 2 * Real.exp (-u) := by
      have hexp : (2 : ℝ) ^ (-c * Real.exp (-u))
          = Real.exp (-c * Real.exp (-u) * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      rw [hexp]
      have h := Real.add_one_le_exp (-c * Real.exp (-u) * Real.log 2)
      linarith
    rw [hrw1]
    have hA : (0 : ℝ) < (2 : ℝ) ^ (-c * Real.exp (-u)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hstep : (2 : ℝ) ^ (-(↑j) * Real.exp (-u)) *
        (1 - (2 : ℝ) ^ (-c * Real.exp (-u)))
        ≤ 1 - (2 : ℝ) ^ (-c * Real.exp (-u)) := by
      have hnn : (0 : ℝ) ≤ 1 - (2 : ℝ) ^ (-c * Real.exp (-u)) := by
        have : (2 : ℝ) ^ (-c * Real.exp (-u)) ≤ 1 := by
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
  have hI3 := integrable_Jint_integrand ((j : ℕ):ℝ) (by positivity) i
  have hfeq : (fun u : ℝ => u ^ i * Real.exp (-u) * Bfun j u)
      = fun u : ℝ =>
        (u ^ i * Real.exp (-u) * (2 : ℝ) ^ (-((j : ℕ):ℝ) * Real.exp (-u))
          - u ^ i * Real.exp (-u))
        + ((j : ℕ):ℝ) * Real.log 2 * (u ^ i * Real.exp (-(2 * u))) := by
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
  have hu0 : (0 : ℝ) < u := hu
  apply mul_le_mul_of_nonneg_left (Bfun_mono j m hjm u)
  positivity

/-- Replace the varying index: sum 2^i betaCirc i (m-i) <= sum 2^i betaCirc i m. -/
theorem sum_betaCirc_le_uniform (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i (m - i)
      ≤ ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i m := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact betaCirc_mono i (m - i) m (Nat.sub_le m i)

/-- The sum of 2^i betaCirc i m is the integral of the partial exponential sum. -/
theorem sum_betaCirc_eq_integral (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i m
      = ∫ u in Set.Ioi (0 : ℝ),
        (∑ i ∈ Finset.range (m + 1), (2 * u) ^ i / (Nat.factorial i))
          * (Real.exp (-u) * Bfun m u) := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (2 : ℝ) ^ i * betaCirc i m
        = ∫ u in Set.Ioi (0 : ℝ),
          ((2 * u) ^ i / (Nat.factorial i)) * (Real.exp (-u) * Bfun m u) := by
    intro i _
    unfold betaCirc
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    have hfac : ((Nat.factorial i : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    simp only [mul_pow]
    field_simp
    try ring
  rw [Finset.sum_congr rfl hterm]
  rw [← MeasureTheory.integral_finsetSum]
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only [Finset.sum_mul]
  · intro i _
    have hb := integrable_betaCirc_integrand i m
    have heq : (fun u : ℝ => ((2 * u) ^ i / (Nat.factorial i)) * (Real.exp (-u) * Bfun m u))
        = fun u : ℝ => ((2 : ℝ) ^ i / (Nat.factorial i)) *
          (u ^ i * Real.exp (-u) * Bfun m u) := by
      funext u
      rw [mul_pow]
      ring
    rw [heq]
    exact hb.const_mul _

/-- e^u * Bfun m u is integrable on (0, infty): it equals
(e^(-(m log2) e^-u) - 1) e^u + m log2, times... -- bounded via the Bfun
decomposition against integrable pieces. -/
theorem integrable_exp_Bfun (m : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp u * Bfun m u) (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi 0) := by
    have hG : MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ ((1 : ℝ) - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (s := (1 : ℝ)) (by norm_num)
    apply hG.congr_fun ?_ measurableSet_Ioi
    intro u _
    simp only
    rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one]
  have hdom : MeasureTheory.IntegrableOn
      (fun u : ℝ => (((m : ℕ):ℝ) * Real.log 2) ^ 2 * Real.exp (-u))
      (Set.Ioi 0) := hbase.const_mul _
  apply MeasureTheory.Integrable.mono hdom
  · apply Measurable.aestronglyMeasurable
    unfold Bfun
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    set x := ((m : ℕ):ℝ) * Real.log 2 * Real.exp (-u) with hx
    have hxnn : (0 : ℝ) ≤ x := by
      rw [hx]
      positivity
    have hBeq : Bfun m u = Real.exp (-x) - 1 + x := by
      unfold Bfun
      rw [hx]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring_nf
    have hquad : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
      rcases le_total x 1 with hx1 | hx1
      · have habs : |(-x)| ≤ 1 := by
          rw [abs_neg, abs_of_nonneg hxnn]
          exact hx1
        have hb := Real.abs_exp_sub_one_sub_id_le habs
        have hb2 : Real.exp (-x) - 1 - (-x) ≤ (-x) ^ 2 :=
          le_trans (le_abs_self _) hb
        nlinarith [hb2]
      · have hle1 : Real.exp (-x) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          linarith
        nlinarith [hle1, hx1]
    have hBnn : (0 : ℝ) ≤ Bfun m u := Bfun_nonneg m u
    have hxsq : x ^ 2 = (((m : ℕ):ℝ) * Real.log 2) ^ 2 * Real.exp (-u) ^ 2 := by
      rw [hx]
      ring
    have hexpsq : Real.exp u * Real.exp (-u) ^ 2 = Real.exp (-u) := by
      rw [show Real.exp (-u) ^ 2 = Real.exp (-u) * Real.exp (-u) by ring,
        ← mul_assoc, ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero, one_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp u * Bfun m u),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤
        (((m : ℕ):ℝ) * Real.log 2) ^ 2 * Real.exp (-u))]
    calc Real.exp u * Bfun m u ≤ Real.exp u * x ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos u).le
          rw [hBeq]
          exact le_trans hquad (by nlinarith [sq_nonneg x])
      _ = (((m : ℕ):ℝ) * Real.log 2) ^ 2 * (Real.exp u * Real.exp (-u) ^ 2) := by
          rw [hxsq]
          ring
      _ = (((m : ℕ):ℝ) * Real.log 2) ^ 2 * Real.exp (-u) := by rw [hexpsq]

/-- The key bound: sum 2^i betaCirc i m <= int e^u Bfun m u. -/
theorem sum_betaCirc_le_integral (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i m
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp u * Bfun m u := by
  rw [sum_betaCirc_eq_integral m]
  apply MeasureTheory.setIntegral_mono_on
  · have heq : (fun u : ℝ =>
        (∑ i ∈ Finset.range (m + 1), (2 * u) ^ i / (Nat.factorial i))
          * (Real.exp (-u) * Bfun m u))
        = fun u : ℝ => ∑ i ∈ Finset.range (m + 1),
          ((2 : ℝ) ^ i / (Nat.factorial i)) * (u ^ i * Real.exp (-u) * Bfun m u) := by
      funext u
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_pow]
      ring
    rw [heq]
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (integrable_betaCirc_integrand i m).const_mul _
  · exact integrable_exp_Bfun m
  · exact measurableSet_Ioi
  · intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hsum := sum_pow_div_factorial_le_exp (2 * u) (by linarith) m
    have hB := Bfun_nonneg m u
    have hE : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
    have hfac : Real.exp (2 * u) * (Real.exp (-u) * Bfun m u)
        = Real.exp u * Bfun m u := by
      rw [show Real.exp (2 * u) * (Real.exp (-u) * Bfun m u)
          = (Real.exp (2 * u) * Real.exp (-u)) * Bfun m u by ring,
        ← Real.exp_add]
      ring_nf
    calc (∑ i ∈ Finset.range (m + 1), (2 * u) ^ i / (Nat.factorial i))
          * (Real.exp (-u) * Bfun m u)
        ≤ Real.exp (2 * u) * (Real.exp (-u) * Bfun m u) := by
          apply mul_le_mul_of_nonneg_right hsum
          positivity
      _ = Real.exp u * Bfun m u := hfac

/-- The map u -> e^(-u) sends (0, infty) onto (0, 1). -/
theorem expNeg_image : (fun u : ℝ => Real.exp (-u)) '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext t
  simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    have h1 : Real.exp (-u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h1
  · rintro ⟨h0, h1⟩
    refine ⟨-Real.log t, ?_, ?_⟩
    · have hlog : Real.log t < 0 := Real.log_neg h0 h1
      linarith
    · show Real.exp (-(-Real.log t)) = t
      rw [neg_neg, Real.exp_log h0]

/-- The map is injective on (0, infty). -/
theorem expNeg_injOn : Set.InjOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi 0) := by
  intro u _ v _ huv
  simp only at huv
  have := Real.exp_injective huv
  linarith

/-- The change of variables t = e^(-u): int_{(0,inf)} e^u Bfun m u du
= int_{(0,1)} (e^(-at) - 1 + at)/t^2 dt with a = m log 2. -/
theorem exp_Bfun_integral_eq (m : ℕ) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp u * Bfun m u)
      = ∫ t in Set.Ioo (0 : ℝ) 1,
        (Real.exp (-(((m : ℕ):ℝ) * Real.log 2 * t)) - 1
          + ((m : ℕ):ℝ) * Real.log 2 * t) / t ^ 2 := by
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.exp (-u))
        (Real.exp (-u) * (-1)) (Set.Ioi 0) u := by
    intro u _
    exact (((hasDerivAt_neg u).exp)).hasDerivWithinAt
  have himg := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv expNeg_injOn
    (fun t : ℝ => (Real.exp (-(((m : ℕ):ℝ) * Real.log 2 * t)) - 1
      + ((m : ℕ):ℝ) * Real.log 2 * t) / t ^ 2)
  rw [expNeg_image] at himg
  rw [himg]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hE : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  simp only [smul_eq_mul, mul_neg_one, abs_neg, abs_of_pos hE]
  have hBeq : Bfun m u
      = (Real.exp (-(((m : ℕ):ℝ) * Real.log 2 * Real.exp (-u))) - 1
        + ((m : ℕ):ℝ) * Real.log 2 * Real.exp (-u)) := by
    unfold Bfun
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hBeq]
  have hsq : Real.exp (-u) ^ 2 ≠ 0 := by positivity
  field_simp
  rw [← Real.exp_add]
  ring_nf
  simp [Real.exp_zero]

/-- MANUSCRIPT THEOREM 4.1, UPPER BOUND: delta_m <= a log a + gamma a - a + 1
- 1 - (log2 / 4) m, where a = m log 2. -/
theorem deltaM_upper_bound (m : ℕ) (hm : 1 ≤ m) :
    deltaM m ≤ -1 - (Real.log 2 / 4) * (m : ℝ)
      + (((m : ℕ):ℝ) * Real.log 2) * Real.log (((m : ℕ):ℝ) * Real.log 2)
      + Real.eulerMascheroniConstant * (((m : ℕ):ℝ) * Real.log 2)
      - ((m : ℕ):ℝ) * Real.log 2 + 1 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmpos : (0 : ℝ) < ((m : ℕ):ℝ) := by
    have : (1 : ℝ) ≤ ((m : ℕ):ℝ) := by exact_mod_cast hm
    linarith
  have hapos : (0 : ℝ) < ((m : ℕ):ℝ) * Real.log 2 := by positivity
  have hIooIoc : (∫ t in Set.Ioo (0 : ℝ) 1,
      (Real.exp (-(((m : ℕ):ℝ) * Real.log 2 * t)) - 1
        + ((m : ℕ):ℝ) * Real.log 2 * t) / t ^ 2)
      = ∫ t in Set.Ioc (0 : ℝ) 1,
        (Real.exp (-(((m : ℕ):ℝ) * Real.log 2) * t) - 1
          + ((m : ℕ):ℝ) * Real.log 2 * t) / t ^ 2 := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro t _
    simp only
    rw [show -(((m : ℕ):ℝ) * Real.log 2) * t = -(((m : ℕ):ℝ) * Real.log 2 * t) by ring]
  have hgap := BanksMartin.gap_five_evaluation (((m : ℕ):ℝ) * Real.log 2) hapos
  have hchain := sum_betaCirc_le_uniform m
  have hchain2 := sum_betaCirc_le_integral m
  have hsubst := exp_Bfun_integral_eq m
  rw [deltaM_identity m]
  have hfinal : ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i (m - i)
      ≤ (((m : ℕ):ℝ) * Real.log 2) * Real.log (((m : ℕ):ℝ) * Real.log 2)
        + Real.eulerMascheroniConstant * (((m : ℕ):ℝ) * Real.log 2)
        - ((m : ℕ):ℝ) * Real.log 2 + 1 := by
    calc ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i (m - i)
        ≤ ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * betaCirc i m := hchain
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp u * Bfun m u := hchain2
      _ = ∫ t in Set.Ioo (0 : ℝ) 1,
          (Real.exp (-(((m : ℕ):ℝ) * Real.log 2 * t)) - 1
            + ((m : ℕ):ℝ) * Real.log 2 * t) / t ^ 2 := hsubst
      _ = ∫ t in Set.Ioc (0 : ℝ) 1,
          (Real.exp (-(((m : ℕ):ℝ) * Real.log 2) * t) - 1
            + ((m : ℕ):ℝ) * Real.log 2 * t) / t ^ 2 := hIooIoc
      _ ≤ _ := hgap
  linarith [hfinal]

/-- The manuscript's c1* = log2 (log log2 + gamma - 1 - 1 / 4) = -0.720386... -/
noncomputable def cStarOne : ℝ :=
  Real.log 2 * (Real.log (Real.log 2) + Real.eulerMascheroniConstant - 1 - 1 / 4)

/-- cStarOne < 0: log(log 2) < 0 since 0 < log 2 < 1, and gamma < 2/3, so
log log 2 + gamma - 5/4 < 0 - 5/4 + 2/3 < 0. -/
theorem cStarOne_neg : cStarOne < 0 := by
  unfold cStarOne
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2lt : Real.log 2 < 1 := by
    have h : Real.log 2 < Real.log (Real.exp 1) := by
      apply Real.log_lt_log (by norm_num)
      have := Real.exp_one_gt_d9
      linarith
    rwa [Real.log_exp] at h
  have hll : Real.log (Real.log 2) < 0 := log_neg hl2 hl2lt
  have hg : Real.eulerMascheroniConstant < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
  have hinner : Real.log (Real.log 2) + Real.eulerMascheroniConstant - 1 - 1 / 4 < 0 := by
    linarith
  exact mul_neg_of_pos_of_neg hl2 hinner

/-- MANUSCRIPT THEOREM 4.1 (upper bound, manuscript form):
delta_m <= (log 2) m log m + c1* m, for m >= 1. -/
theorem deltaM_upper_bound_manuscript (m : ℕ) (hm : 1 ≤ m) :
    deltaM m ≤ Real.log 2 * (m : ℝ) * Real.log (m : ℝ) + cStarOne * (m : ℝ) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (1 : ℝ) ≤ ((m : ℕ):ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < ((m : ℕ):ℝ) := by linarith
  have hub := deltaM_upper_bound m hm
  have hlogsplit : Real.log (((m : ℕ):ℝ) * Real.log 2)
      = Real.log ((m : ℕ):ℝ) + Real.log (Real.log 2) := by
    rw [Real.log_mul (ne_of_gt hmpos) (ne_of_gt hl2)]
  rw [hlogsplit] at hub
  unfold cStarOne
  nlinarith [hub, hl2, hmpos]

/-- MANUSCRIPT THEOREM 4.1, uniform form: |delta_m| <= D(m).

Upper: the proved bound is log2 m log m + cStarOne m, and cStarOne < 0
(cStarOne_neg), so it lies below D(m) = log2 m log(m+1) + 1.
Lower: -1 - (log2/4) m >= -D(m), since log2 m log(m+1) >= (log2/4) m for m >= 1
(log(m+1) >= log 2 >= 1/4).
m = 0 is the anchor: delta_0 = -1 and D(0) = 1. -/
theorem deltaM_abs_le (m : ℕ) : |deltaM m| ≤ DBound m := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    rw [deltaM_zero]
    unfold DBound
    norm_num
  · have hlow := deltaM_lower_bound m
    have hup := deltaM_upper_bound_manuscript m hm
    have hcs := cStarOne_neg
    have hmR : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlogm1 : Real.log 2 ≤ Real.log ((m : ℝ) + 1) := by
      apply Real.log_le_log (by norm_num)
      linarith
    have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
      apply Real.log_le_log (by linarith)
      linarith
    have hl2q : (1:ℝ) / 4 ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    unfold DBound
    rw [abs_le]
    have hm0 : (0:ℝ) ≤ (m : ℝ) := by linarith
    have hkey1 : Real.log 2 / 4 * (m : ℝ)
        ≤ Real.log 2 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
      have hq : Real.log 2 / 4 ≤ Real.log 2 * Real.log ((m : ℝ) + 1) := by
        nlinarith [hl2, hlogm1, hl2q]
      nlinarith [hq, hm0]
    have hkey2 : Real.log 2 * (m : ℝ) * Real.log (m : ℝ)
        ≤ Real.log 2 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left hlogm
      positivity
    have hkey3 : cStarOne * (m : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcs) hm0
    constructor
    · linarith [hlow, hkey1]
    · linarith [hup, hkey2, hkey3]

/-- BRIDGE: for a function with a power series on a ball, analytic everywhere,
the n-th iterated (one-dimensional) derivative at the center is n! times the
n-th coefficient. This is the Taylor-coefficient relation Mathlib does not
state directly for `iteratedDeriv`. -/
theorem iteratedDeriv_eq_factorial_smul_coeff
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f p 0 r) (h' : AnalyticOn ℂ f Set.univ) (n : ℕ) :
    iteratedDeriv n f 0 = (Nat.factorial n : ℂ) * p.coeff n := by
  have hv := h.iteratedFDeriv_eq_sum h' (v := fun _ : Fin n => (1 : ℂ))
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hv]
  have hconst : ∀ σ : Equiv.Perm (Fin n),
      p n (fun i => (fun _ : Fin n => (1 : ℂ)) (σ i)) = p.coeff n := by
    intro σ
    rfl
  rw [Finset.sum_congr rfl (fun σ _ => hconst σ)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [nsmul_eq_mul]

/-- Taylor bridge without a global analyticity hypothesis: over a complete
space, HasFPowerSeriesOnBall alone determines the iterated derivatives.
Weakening of iteratedDeriv_eq_factorial_smul_coeff, which required
AnalyticOn C f univ and so could not be applied to functions with poles
(e.g. G2C, whose nearest pole is at z = 3). -/
theorem iteratedDeriv_eq_factorial_smul_coeff'
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f p 0 r) (n : ℕ) :
    iteratedDeriv n f 0 = (Nat.factorial n : ℂ) * p.coeff n := by
  have hv := h.iteratedFDeriv_eq_sum_of_completeSpace (v := fun _ : Fin n => (1 : ℂ))
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hv]
  have hconst : ∀ σ : Equiv.Perm (Fin n),
      p n (fun i => (fun _ : Fin n => (1 : ℂ)) (σ i)) = p.coeff n := by
    intro σ
    rfl
  rw [Finset.sum_congr rfl (fun σ _ => hconst σ)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [nsmul_eq_mul]

/-- Pointwise version away from the pole. -/
theorem deriv_geom_family_at (c : ℂ) (hc : c ≠ 0) (k : ℕ) (z : ℂ)
    (hz : 1 - z / c ≠ 0) :
    deriv (fun w : ℂ => (Nat.factorial k : ℂ) / (c ^ k * (1 - w / c) ^ (k + 1))) z
      = (Nat.factorial (k + 1) : ℂ) / (c ^ (k + 1) * (1 - z / c) ^ (k + 2)) := by
  have hbase : HasDerivAt (fun w : ℂ => 1 - w / c) (-(1 / c)) z := by
    have h1 : HasDerivAt (fun w : ℂ => w / c) (1 / c) z := by
      simpa using (hasDerivAt_id z).div_const c
    simpa [Pi.sub_def] using (hasDerivAt_const z (1 : ℂ)).sub h1
  have hpow : HasDerivAt (fun w : ℂ => (1 - w / c) ^ (k + 1))
      (((k : ℂ) + 1) * (1 - z / c) ^ k * (-(1 / c))) z := by
    have hp := hbase.pow (k + 1)
    simpa [Pi.pow_def] using hp
  have hden : c ^ k * (1 - z / c) ^ (k + 1) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hc)
    exact pow_ne_zero _ hz
  have hmul : HasDerivAt (fun w : ℂ => c ^ k * (1 - w / c) ^ (k + 1))
      (c ^ k * (((k : ℂ) + 1) * (1 - z / c) ^ k * (-(1 / c)))) z :=
    hpow.const_mul _
  have hdiv0 := (hasDerivAt_const z ((Nat.factorial k : ℂ))).div hmul hden
  have hdiv : HasDerivAt (fun w : ℂ => (Nat.factorial k : ℂ) / (c ^ k * (1 - w / c) ^ (k + 1)))
      ((0 * (c ^ k * (1 - z / c) ^ (k + 1))
        - (Nat.factorial k : ℂ) * (c ^ k * (((k : ℂ) + 1) * (1 - z / c) ^ k * (-(1 / c)))))
        / (c ^ k * (1 - z / c) ^ (k + 1)) ^ 2) z := by
    simpa [Pi.div_def] using hdiv0
  rw [hdiv.deriv]
  set w := 1 - z / c with hw
  have hwnz : w ≠ 0 := hz
  have hnum : (0 * (c ^ k * w ^ (k + 1))
      - (Nat.factorial k : ℂ) * (c ^ k * (((k : ℂ) + 1) * w ^ k * (-(1 / c)))))
      / (c ^ k * w ^ (k + 1)) ^ 2
      = ((Nat.factorial k : ℂ) * ((k : ℂ) + 1)) / (c ^ (k + 1) * w ^ (k + 2)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  rw [hnum]
  congr 1
  push_cast [Nat.factorial_succ]
  ring

theorem iteratedDeriv_geom (c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (1 - z / c)⁻¹) 0
      = (Nat.factorial n : ℂ) / c ^ n := by
  have hopen : IsOpen {z : ℂ | 1 - z / c ≠ 0} := by
    have hcont : Continuous (fun z : ℂ => 1 - z / c) := by fun_prop
    exact isOpen_ne_fun hcont continuous_const
  have hmem : (0 : ℂ) ∈ {z : ℂ | 1 - z / c ≠ 0} := by
    simp
  have hfam : ∀ k : ℕ, ∀ z ∈ {z : ℂ | 1 - z / c ≠ 0},
      iteratedDeriv k (fun w : ℂ => (1 - w / c)⁻¹) z
        = (Nat.factorial k : ℂ) / (c ^ k * (1 - z / c) ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
      intro z hz
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul,
        zero_add, pow_one]
      rw [one_div]
    | succ K ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hloc : ∀ᶠ w in nhds z,
          iteratedDeriv K (fun v : ℂ => (1 - v / c)⁻¹) w
            = (Nat.factorial K : ℂ) / (c ^ K * (1 - w / c) ^ (K + 1)) := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact ih w hw
      rw [Filter.EventuallyEq.deriv_eq hloc]
      exact deriv_geom_family_at c hc K z hz
  have := hfam n 0 hmem
  rw [this]
  simp

/-!
## Manuscript Lemma 2.2 (the exact expansion) -- SCAFFOLD

Target (manuscript Lemma 2.2): for s in (1, 2],

  F_k(s) = sum_{i+j+l=k} g_i(s) * 2^(-j s) * (-log(s-1))^l / l!

where g_i(s) = [z^i] G2(s,z), and F(s,z) = (s-1)^(-z) (1 - z / 2^s)^(-1) G2(s,z).

The proof factors into four obligations:

L1 (generating function): the Dirichlet series with z-weighting equals the
   Euler product, i.e. sum_n z^Omega(n) n^(-s) = prod_p (1 - z p^(-s))^(-1),
   for s > 1 and |z| < 2^s.  [Mathlib's EulerProduct machinery is the likely
   route; this is the substantial piece.]

L2 (coefficient extraction): F_k(s), defined as the tsum over k-almost-primes
   of n^(-s), is the k-th Taylor coefficient in z of that generating function.

L3 (the three factors): the z-power series of (s-1)^(-z), of (1 - z / 2^s)^(-1),
   and of G2(s,z), with their radii (entire, 2^s, 3^s respectively).

L4 (Cauchy product): the coefficient of z^k in a product of three power series
   is the triple convolution, given absolute convergence on |z| <= 1.5.
-/

/-- The z-weighted completely multiplicative function n -> z^Omega(n) n^(-s),
bundled as a monoid-with-zero hom for Mathlib's Euler product machinery. -/
noncomputable def zOmegaHom (s : ℝ) (z : ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else z ^ (bigOmega n) * ((n : ℂ) ^ (-(s : ℂ)))
  map_zero' := by simp
  map_one' := by
    simp only [if_neg (one_ne_zero)]
    have hO : bigOmega 1 = 0 := by
      unfold bigOmega
      simp
    rw [hO, pow_zero, one_mul]
    norm_num
  map_mul' := by
    intro a b
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hb : b = 0
      · simp [hb]
      · have hab : a * b ≠ 0 := mul_ne_zero ha hb
        simp only [if_neg ha, if_neg hb, if_neg hab]
        rw [bigOmega_mul a b ha hb, pow_add]
        have hcast : (((a * b : ℕ) : ℂ)) = (a : ℂ) * (b : ℂ) := by
          push_cast
          ring
        rw [hcast]
        have hbridge : ((a : ℂ) * (b : ℂ)) ^ (-(s : ℂ))
            = (a : ℂ) ^ (-(s : ℂ)) * (b : ℂ) ^ (-(s : ℂ)) := by
          have hA : ((a : ℕ) : ℂ) = (((a : ℕ) : ℝ) : ℂ) := by push_cast; ring
          have hB : ((b : ℕ) : ℂ) = (((b : ℕ) : ℝ) : ℂ) := by push_cast; ring
          rw [hA, hB]
          exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) _
        rw [hbridge]
        ring


/-- OBLIGATION L3a: the (s-1)^(-z) factor's coefficients. -/
theorem coeff_pow_neg (s : ℝ) (hs : 1 < s) (l : ℕ) :
    (iteratedDeriv l (fun z : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-z)) 0)
        / (Nat.factorial l : ℂ)
      = ((-Real.log (s - 1)) ^ l / (Nat.factorial l) : ℝ) := by
  have hspos : (0 : ℝ) < s - 1 := by linarith
  have hsne : ((s - 1 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hrewrite : (fun z : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-z))
      = fun z : ℂ => Complex.exp ((-(Real.log (s - 1) : ℂ)) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hsne]
    congr 1
    rw [← Complex.ofReal_log (le_of_lt hspos)]
    ring
  rw [hrewrite, iteratedDeriv_cexp_const_mul l (-(Real.log (s - 1) : ℂ))]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  have hfacnz : ((Nat.factorial l : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  push_cast
  ring

/-- OBLIGATION L3b: the (1 - z / 2^s)^(-1) factor's coefficients. -/
theorem coeff_geom (s : ℝ) (hs : 1 < s) (j : ℕ) :
    (iteratedDeriv j (fun z : ℂ => (1 - z / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0)
        / (Nat.factorial j : ℂ)
      = ((2 : ℝ) ^ (-(j : ℝ) * s) : ℝ) := by
  have hcnz : ((2 : ℂ) ^ (s : ℂ)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro hcon
    exact absurd hcon.1 (by norm_num)
  rw [iteratedDeriv_geom ((2 : ℂ) ^ (s : ℂ)) hcnz j]
  have hfacnz : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [div_div, mul_comm, ← div_div, div_self hfacnz]
  rw [one_div]
  have hreal : ((2 : ℂ) ^ (s : ℂ)) = (((2 : ℝ) ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hreal]
  rw [← Complex.ofReal_pow]
  rw [← Complex.ofReal_inv]
  norm_cast
  rw [← Real.rpow_natCast ((2 : ℝ) ^ s) j, ← Real.rpow_mul (by norm_num)]
  rw [← Real.rpow_neg (by norm_num)]
  congr 1
  push_cast
  ring


/-!
### L2, restated

The manuscript's Lemma 2.2 proof does not go through a Dirichlet-series Euler
product.  It uses the *definitional* factorization

  F(s,z) = (s-1)^(-z) * (1 - z / 2^s)^(-1) * G2(s,z)

together with the radii of the three factors (entire, 2^s, 3^s), all absolutely
convergent on |z| <= 1.5, and reads off the k-th coefficient as the triple
convolution.  The two obligations are therefore:

  L2a: F_k(s) is the k-th Taylor coefficient of z -> Fbig s z, where
       Fbig s z := (s-1)^(-z) * (1 - z / 2^s)^(-1) * G2C s z.
       (This is where the Dirichlet series meets the Euler product; it is the
       one genuinely number-theoretic step.)

  L2b: the Cauchy product of the three factors, using coeff_pow_neg (proven),
       coeff_geom (proven), and gCoeff, valid on |z| <= 1.5 where all three
       are analytic (G2C_differentiableOn gives radius 2 > 1.5).
-/

/-- c(s) = prod_{p >= 3} (1 - p^(-s))^(-1) = zeta(s)(1 - 2^(-s)).
This is the constant whose z-th power is the first factor of F(s,z)
when G2 is normalised as our G2C (product over p >= 3 of the
regularised factors). -/
noncomputable def cFac (s : ℝ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (1 - (p : ℝ) ^ (-s))⁻¹

/-- Coefficients of the factor c^z: the l-th is (log c)^l / l!. -/
theorem coeff_cpow (s : ℝ) (hc : 0 < cFac s) (l : ℕ) :
    (iteratedDeriv l (fun z : ℂ => ((cFac s : ℝ) : ℂ) ^ z) 0) / (Nat.factorial l : ℂ)
      = (((Real.log (cFac s)) ^ l / (Nat.factorial l) : ℝ) : ℂ) := by
  have hcne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hc
  have hrewrite : (fun z : ℂ => ((cFac s : ℝ) : ℂ) ^ z)
      = fun z : ℂ => Complex.exp (((Real.log (cFac s) : ℝ) : ℂ) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hcne]
    congr 1
    rw [← Complex.ofReal_log (le_of_lt hc)]
    try ring
  rw [hrewrite, iteratedDeriv_cexp_const_mul l ((Real.log (cFac s) : ℝ) : ℂ)]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  push_cast
  ring

/-- The cFac family is multipliable for s > 1.
Needed because 0 < cFac s has been threaded as a hypothesis throughout;
without multipliability that would be an assumption about a tprod junk value. -/
theorem cFac_multipliable (s : ℝ) (hs : 1 < s) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹) := by
  have hthird : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      ((p : ℕ):ℝ) ^ (-s) ≤ 1 / 3 := by
    intro p
    have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
    have h1 : ((p : ℕ):ℝ) ^ (-s) ≤ ((p : ℕ):ℝ) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : (((p : ℕ):ℝ))⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (0 : ℝ) < ((p : ℕ):ℝ) ^ (-s) := by
    intro p
    have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
    positivity
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (3 / 2) * (((p : ℕ):ℝ) ^ (-s))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (hbase.subtype _).mul_left _
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ - 1) := by
    apply Summable.of_nonneg_of_le _ _ hcomp
    · intro p
      have h3 := hthird p
      have hp := hpos p
      have hden : (0 : ℝ) < 1 - ((p : ℕ):ℝ) ^ (-s) := by linarith
      rw [sub_nonneg, le_inv_comm₀ (by norm_num) hden]
      linarith
    · intro p
      have h3 := hthird p
      have hp := hpos p
      have hden : (0 : ℝ) < 1 - ((p : ℕ):ℝ) ^ (-s) := by linarith
      have hkey : (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ - 1
          = ((p : ℕ):ℝ) ^ (-s) / (1 - ((p : ℕ):ℝ) ^ (-s)) := by
        field_simp
        ring
      rw [hkey, div_le_iff₀ hden]
      nlinarith
  have h := Real.multipliable_one_add_of_summable hsum
  apply h.congr
  intro p
  ring

/-- The regularised zeta factor: (s-1) * zeta(s), extended by 1 at s = 1.
Smooth on [1, infinity) by GLW Lemma 11 / the standard pole structure; here we
only need the value at 1, which holds definitionally.  Real-valued because
zeta is real on the real axis for s > 1. -/
noncomputable def zetaTilde (s : ℝ) : ℝ :=
  if s = 1 then 1 else (s - 1) * (riemannZeta (s : ℂ)).re

/-- The extension is by the residue: zetaTilde 1 = 1 definitionally. -/
theorem zetaTilde_one : zetaTilde 1 = 1 := by
  unfold zetaTilde
  simp

/-- Manuscript normalisation bridge: kappa s = (s-1) * cFac s.
Then the manuscript's G2(s,z) = kappa(s)^z * G2C(s,z), and kappa(1) = 1 / 2,
recovering G2(1,z) = 2^(-z) * prod_{p>2} (...) of section 3.2. -/
noncomputable def kappaFac (s : ℝ) : ℝ := (s - 1) * cFac s

/-- kappa is positive on (1,2]. -/
theorem kappaFac_pos (s : ℝ) (hs : 1 < s) (hc : 0 < cFac s) : 0 < kappaFac s := by
  unfold kappaFac
  have h1 : (0 : ℝ) < s - 1 := by linarith
  positivity

/-- The manuscript's G2, expressed through our G2C. -/
noncomputable def G2manu (s : ℝ) (z : ℂ) : ℂ :=
  ((kappaFac s : ℝ) : ℂ) ^ z * G2C s z

/-- The full generating function, as the product of its three factors. -/
noncomputable def Fbig (s : ℝ) (z : ℂ) : ℂ :=
  ((cFac s : ℝ) : ℂ) ^ z * (1 - z / ((2 : ℂ) ^ (s : ℂ)))⁻¹ * G2C s z


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
      prod_p (1 - z p^-s)^-1 = (s-1)^(-z) (1 - z / 2^s)^(-1) G2C s z.
    This is the content of the manuscript's section 3.2 / GLW Lemma 11:
    G2 is DEFINED as the regularised tail, so this should reduce to the
    definition of G2C plus the zeta factor.  Check Banksmartin's G2C
    definition (line ~1066) before proving.

A4  Coefficient extraction: F_k(s) (a tsum over k-almost-primes) is the
    k-th Taylor coefficient of z -> tsum_n z^Omega(n) n^(-s).  This is
    where "collect the terms with Omega(n) = k" happens; needs the
    analyticity of the tsum in z on |z| < 2^s.
-/

/-- Omega(p^n) = n for p prime. -/
lemma bigOmega_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) : bigOmega (p ^ n) = n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    unfold bigOmega
    simp
  | succ N ih =>
    have hpn : p ^ N ≠ 0 := pow_ne_zero N hp.pos.ne'
    have hp0 : p ≠ 0 := hp.pos.ne'
    rw [pow_succ, bigOmega_mul (p ^ N) p hpn hp0, ih]
    have hO : bigOmega p = 1 := by
      unfold bigOmega
      rw [hp.factorization]
      simp
    rw [hO]

theorem zOmega_prime_summable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) {p : ℕ} (hp : p.Prime) :
    Summable (fun n : ℕ => Norm.norm (zOmegaHom s z (p ^ n))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.two_le
  have hratio : Norm.norm z * ((p : ℝ) ^ (-s)) < 1 := by
    have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hps : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := by
      rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ (p : ℝ)),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      gcongr
    have hinv : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
    calc Norm.norm z * ((p : ℝ) ^ (-s)) ≤ Norm.norm z * ((2 : ℝ) ^ (-s)) := by
          apply mul_le_mul_of_nonneg_left hps hznn
      _ = Norm.norm z * ((2 : ℝ) ^ s)⁻¹ := by rw [hinv]
      _ < 1 := by
          have hinvpos : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
          have hkey : Norm.norm z * ((2 : ℝ) ^ s)⁻¹ < ((2 : ℝ) ^ s) * ((2 : ℝ) ^ s)⁻¹ := by
            exact mul_lt_mul_of_pos_right hz hinvpos
          rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
  have hterm : ∀ n : ℕ,
      Norm.norm (zOmegaHom s z (p ^ n)) = (Norm.norm z * ((p : ℝ) ^ (-s))) ^ n := by
    intro n
    have hpn : (p : ℕ) ^ n ≠ 0 := pow_ne_zero n hp.pos.ne'
    have hppos : 0 < (p : ℕ) ^ n := Nat.pos_of_ne_zero hpn
    change Norm.norm (if (p : ℕ) ^ n = 0 then 0
      else z ^ (bigOmega ((p : ℕ) ^ n)) * ((((p : ℕ) ^ n : ℕ) : ℂ) ^ (-(s : ℂ)))) = _
    rw [if_neg hpn, bigOmega_prime_pow hp n, norm_mul, norm_pow]
    rw [Complex.norm_natCast_cpow_of_pos hppos]
    rw [Complex.neg_re, Complex.ofReal_re]
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast ((p : ℝ)) n, ← Real.rpow_mul (Nat.cast_nonneg p)]
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) n, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    ring
  have hgeo : Summable (fun n : ℕ => (Norm.norm z * ((p : ℝ) ^ (-s))) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hratio
  exact hgeo.congr (fun n => (hterm n).symm)

/-- The norm of the z-weighted family, bundled as a real monoid-with-zero hom. -/
noncomputable def zOmegaNormHom (s : ℝ) (z : ℂ) : ℕ →*₀ ℝ where
  toFun n := Norm.norm (zOmegaHom s z n)
  map_zero' := by
    simp only [map_zero, norm_zero]
  map_one' := by
    simp only [map_one, norm_one]
  map_mul' := by
    intro a b
    simp only [map_mul, norm_mul]

/-- The norm bundle agrees with the norm of the complex bundle. -/
theorem zOmegaNormHom_apply (s : ℝ) (z : ℂ) (n : ℕ) :
    zOmegaNormHom s z n = Norm.norm (zOmegaHom s z n) := rfl

/-- The norm of the family at a prime power is a geometric term. -/
theorem zOmegaNorm_prime_pow (s : ℝ) (z : ℂ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    zOmegaNormHom s z (p ^ n) = (Norm.norm z * ((p : ℝ) ^ (-s))) ^ n := by
  rw [zOmegaNormHom_apply]
  have hpn : (p : ℕ) ^ n ≠ 0 := pow_ne_zero n hp.pos.ne'
  have hppos : 0 < (p : ℕ) ^ n := Nat.pos_of_ne_zero hpn
  change Norm.norm (if (p : ℕ) ^ n = 0 then 0
    else z ^ (bigOmega ((p : ℕ) ^ n)) * ((((p : ℕ) ^ n : ℕ) : ℂ) ^ (-(s : ℂ)))) = _
  rw [if_neg hpn, bigOmega_prime_pow hp n, norm_mul, norm_pow]
  rw [Complex.norm_natCast_cpow_of_pos hppos]
  rw [Complex.neg_re, Complex.ofReal_re]
  rw [Nat.cast_pow]
  rw [←  Real.rpow_natCast ((p : ℝ)) n, ←  Real.rpow_mul (Nat.cast_nonneg p)]
  rw [mul_pow]
  congr 1
  rw [←  Real.rpow_natCast ((p : ℝ) ^ (-s)) n, ←  Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  ring

/-- A1 step 2: for each N, the family is summable over N-smooth numbers. -/
theorem zOmega_smooth_summable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) (N : ℕ) :
    Summable (fun m : N.smoothNumbers => Norm.norm (zOmegaHom s z m)) := by
  have hf1 : zOmegaHom s z 1 = 1 := map_one _
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      zOmegaHom s z (a * b) = zOmegaHom s z a * zOmegaHom s z b := by
    intro a b _
    exact map_mul _ a b
  have hprime : ∀ {p : ℕ}, p.Prime →
      Summable (fun n : ℕ => Norm.norm (zOmegaHom s z (p ^ n))) := by
    intro p hp
    exact zOmega_prime_summable s hs z hz hp
  exact (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hprime N).1

/-- A1 step 3a: the scaled prime sum converges. -/
theorem zOmega_prime_sum_summable (s : ℝ) (hs : 1 < s) (z : ℂ) :
    Summable (fun p : Nat.Primes => Norm.norm z * ((p : ℝ) ^ (-s))) := by
  have hbase : Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-s))) := by
    rw [Nat.Primes.summable_rpow]
    linarith
  exact hbase.mul_left _

/-- For 0 <= x <= 1 / 2, we have -log(1-x) <= 2x.
Route: 1 - x >= exp(-2x), since exp(-2x) <= 1/(1+2x) <= 1-x when x <= 1 / 2. -/
theorem neg_log_one_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hone : (0 : ℝ) < 1 - x := by linarith
  have hstep1 : Real.exp (-(2*x)) ≤ 1 / (1 + 2*x) := by
    have hpos : (0 : ℝ) < 1 + 2*x := by linarith
    have hexp : 1 + 2*x ≤ Real.exp (2*x) := by
      have := Real.add_one_le_exp (2*x)
      linarith
    have hexpneg : Real.exp (-(2*x)) = (Real.exp (2*x))⁻¹ := by
      rw [Real.exp_neg]
    rw [hexpneg, one_div]
    gcongr
  have hstep2 : (1 : ℝ) / (1 + 2*x) ≤ 1 - x := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + 2*x)]
    nlinarith [hx0, hx]
  have hle : Real.exp (-(2*x)) ≤ 1 - x := le_trans hstep1 hstep2
  have hlog : -(2*x) ≤ Real.log (1 - x) := by
    have := Real.log_le_log (Real.exp_pos (-(2*x))) hle
    rwa [Real.log_exp] at this
  linarith

/-- Each cFac factor is positive, and its argument is at most 1 / 3, for s > 1. -/
theorem cFac_factor_le_third (s : ℝ) (hs : 1 < s) (p : {p : ℕ // p.Prime ∧ 3 ≤ p}) :
    ((p : ℕ):ℝ) ^ (-s) ≤ 1 / 3 ∧ 0 < ((p : ℕ):ℝ) ^ (-s) := by
  have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
  constructor
  · have h1 : ((p : ℕ):ℝ) ^ (-s) ≤ ((p : ℕ):ℝ) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : (((p : ℕ):ℝ))⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  · positivity

/-- The logs of the cFac factors are summable: -log(1-x) <= 2x for x <= 1 / 2,
and x = p^(-s) is p-series summable. -/
theorem cFac_log_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      2 * (((p : ℕ):ℝ) ^ (-s))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (hbase.subtype _).mul_left _
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro p
    obtain ⟨ h3, hp ⟩ := cFac_factor_le_third s hs p
    apply Real.log_nonneg
    rw [le_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  · intro p
    obtain ⟨ h3, hp ⟩ := cFac_factor_le_third s hs p
    rw [Real.log_inv]
    have hkey := neg_log_one_sub_le (((p : ℕ):ℝ) ^ (-s)) (le_of_lt hp) (by linarith)
    linarith

/-- cFac s = exp of the convergent sum of logs, hence positive.
DISCHARGES the hc : 0 < cFac s hypothesis threaded through A3 and Lemma 2.2. -/
theorem cFac_eq_exp_log_sum (s : ℝ) (hs : 1 < s) :
    cFac s = Real.exp (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)) := by
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ := by
    intro p
    obtain ⟨ h3, hp ⟩ := cFac_factor_le_third s hs p
    apply inv_pos.mpr
    linarith
  have hlog := cFac_log_summable s hs
  have hprod := hasProd_of_hasSum_log hpos hlog.hasSum
  unfold cFac
  exact hprod.tprod_eq

theorem cFac_pos (s : ℝ) (hs : 1 < s) : 0 < cFac s := by
  rw [cFac_eq_exp_log_sum s hs]
  exact Real.exp_pos _

/-- The real cFac product, cast to C, is the complex product over p >= 3. -/
theorem cFac_ofReal (s : ℝ) (hs : 1 < s) :
    ((cFac s : ℝ) : ℂ)
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (1 - (((p : ℕ):ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹ := by
  have hm := cFac_multipliable s hs
  unfold cFac
  have hmap : ((∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ : ℝ) : ℂ)
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, ((((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ : ℝ)) : ℂ) :=
    hm.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  rw [hmap]
  apply tprod_congr
  intro p
  have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
  have h3 := (cFac_factor_le_third s hs p).1
  have hden : (0 : ℝ) < 1 - ((p : ℕ):ℝ) ^ (-s) := by linarith
  push_cast
  congr 1
  rw [Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ ((p : ℕ):ℝ))]
  push_cast
  ring

/-- The complex form of the p >= 3 Euler family is multipliable for s > 1,
by mapping the real one through the ofReal ring hom. -/
theorem cFac_multipliable_complex (s : ℝ) (hs : 1 < s) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - (((p : ℕ):ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹) := by
  have hm := cFac_multipliable s hs
  have hmap := hm.map Complex.ofRealHom Complex.continuous_ofReal
  apply hmap.congr
  intro p
  have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
  change ((((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ : ℝ)) : ℂ) = _
  push_cast
  congr 1
  rw [Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ ((p : ℕ):ℝ))]
  push_cast
  ring

/-- Probe: does Mathlib's Nat.Primes-indexed Euler product typecheck against
tprod_split_two's {p // p.Prime} spelling without a bridge? -/
theorem zeta_split_probe (s : ℝ) (hs : 1 < s) :
    (∏' p : {p : ℕ // p.Prime}, (1 - (((p : ℕ):ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹)
      = riemannZeta (s : ℂ) := by
  have hre : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  have h := riemannZeta_eulerProduct_tprod hre
  rw [← h]
  apply tprod_congr
  intro p
  congr 1

/-- For s > 1 the p = 2 Euler factor is nonzero. -/
theorem two_factor_ne_one (s : ℝ) (hs : 1 < s) :
    (1 : ℂ) - ((2 : ℂ)) ^ (-(s : ℂ)) ≠ 0 := by
  have hlt : Norm.norm (((2 : ℂ)) ^ (-(s : ℂ))) < 1 := by
    rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h2 : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h2
    linarith
  intro hcon
  have heq : ((2 : ℂ)) ^ (-(s : ℂ)) = 1 := (sub_eq_zero.mp hcon).symm
  rw [heq] at hlt
  simp at hlt

theorem zOmega_factors_multipliable (s : ℝ) (hs : 1 < s) (z : ℂ) :
    Multipliable (fun p : Nat.Primes =>
      (1 - Norm.norm z * (((p : ℕ):ℝ) ^ (-s)))⁻¹) := by
  have hsum := zOmega_prime_sum_summable s hs z
  have hnn : ∀ p : Nat.Primes, (0 : ℝ) ≤ Norm.norm z * (((p : ℕ):ℝ) ^ (-s)) := by
    intro p
    positivity
  have hhalf : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      Norm.norm z * (((p : ℕ):ℝ) ^ (-s)) ≤ 1 / 2 :=
    hsum.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hpos : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      (0 : ℝ) < (1 - Norm.norm z * (((p : ℕ):ℝ) ^ (-s)))⁻¹ := by
    filter_upwards [hhalf] with p hp
    apply inv_pos.mpr
    linarith
  have hlogsum : Summable (fun p : Nat.Primes =>
      Real.log ((1 - Norm.norm z * (((p : ℕ):ℝ) ^ (-s)))⁻¹)) := by
    have hbound : ∀ᶠ p : Nat.Primes in Filter.cofinite,
        Norm.norm (Real.log ((1 - Norm.norm z * (((p : ℕ):ℝ) ^ (-s)))⁻¹))
          ≤ 2 * (Norm.norm z * (((p : ℕ):ℝ) ^ (-s))) := by
      filter_upwards [hhalf] with p hp
      have hx0 : (0 : ℝ) ≤ Norm.norm z * (((p : ℕ):ℝ) ^ (-s)) := hnn p
      have hone : (0 : ℝ) < 1 - Norm.norm z * (((p : ℕ):ℝ) ^ (-s)) := by linarith
      rw [Real.log_inv, Real.norm_eq_abs, abs_neg,
        abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
      exact neg_log_one_sub_le _ hx0 hp
    have hsum2 : Summable (fun p : Nat.Primes =>
        2 * (Norm.norm z * (((p : ℕ):ℝ) ^ (-s)))) := hsum.mul_left 2
    exact Summable.of_norm_bounded_eventually hsum2 hbound
  exact Real.multipliable_of_summable_log' hpos hlogsum

/-- A1 step 4a: membership — naturals below N are N-smooth. -/
theorem mem_smoothNumbers_of_lt (N m : ℕ) (hm : 0 < m) (hlt : m < N) :
    m ∈ N.smoothNumbers := by
  rw [Nat.mem_smoothNumbers]
  refine ⟨ hm.ne', ?_⟩
  intro p hp
  have hpm : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
  exact lt_of_le_of_lt (Nat.le_of_dvd hm hpm) hlt

/-- A1 step 4b: each Euler factor is at least 1. -/
theorem zOmega_factor_ge_one (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) ≤ (1 - Norm.norm z * ((p : ℝ) ^ (-s)))⁻¹ := by
  have hlt : Norm.norm z * ((p : ℝ) ^ (-s)) < 1 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hps : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := by
      rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ (p : ℝ)),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      gcongr
    have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
    have hinvpos : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
    calc Norm.norm z * ((p : ℝ) ^ (-s)) ≤ Norm.norm z * ((2 : ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_left hps hznn
      _ = Norm.norm z * ((2 : ℝ) ^ s)⁻¹ := by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      _ < 1 := by
          have hkey := mul_lt_mul_of_pos_right hz hinvpos
          rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
  have hnn : (0 : ℝ) ≤ Norm.norm z * ((p : ℝ) ^ (-s)) := by positivity
  rw [le_inv_comm₀ (by norm_num) (by linarith)]
  linarith

/-- A1 step 4c: the sum of norms over N-smooth numbers equals the partial
Euler product over primes below N. -/
theorem zOmegaNorm_smooth_hasSum (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) (N : ℕ) :
    HasSum (fun m : N.smoothNumbers => zOmegaNormHom s z m)
      (∏ p ∈ N.primesBelow, ∑' n : ℕ, zOmegaNormHom s z (p ^ n)) := by
  have hf1 : zOmegaNormHom s z 1 = 1 := map_one _
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      zOmegaNormHom s z (a * b) = zOmegaNormHom s z a * zOmegaNormHom s z b := by
    intro a b _
    exact map_mul _ a b
  have hprime : ∀ {p : ℕ}, p.Prime →
      Summable (fun n : ℕ => Norm.norm (zOmegaNormHom s z (p ^ n))) := by
    intro p hp
    have h := zOmega_prime_summable s hs z hz hp
    apply h.congr
    intro n
    rw [zOmegaNormHom_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hprime N).2

/-- A1 step 4d: the inner tsum is the closed geometric form. -/
theorem zOmegaNorm_inner_tsum (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) {p : ℕ} (hp : p.Prime) :
    (∑' n : ℕ, zOmegaNormHom s z (p ^ n))
      = (1 - Norm.norm z * ((p : ℝ) ^ (-s)))⁻¹ := by
  have hratio : Norm.norm z * ((p : ℝ) ^ (-s)) < 1 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hps : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p : ℝ)),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      gcongr
    have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
    have hinvpos : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
    calc Norm.norm z * ((p : ℝ) ^ (-s)) ≤ Norm.norm z * ((2 : ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_left hps hznn
      _ = Norm.norm z * ((2 : ℝ) ^ s)⁻¹ := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      _ < 1 := by
          have hkey := mul_lt_mul_of_pos_right hz hinvpos
          rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey
  have hnn : (0 : ℝ) ≤ Norm.norm z * ((p : ℝ) ^ (-s)) := by positivity
  rw [tsum_congr (fun n => zOmegaNorm_prime_pow s z hp n)]
  exact tsum_geometric_of_lt_one hnn hratio

/-- The per-prime norm bound, in the form the geometric machinery wants. -/
theorem zOmegaNorm_prime_lt_one (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) {p : ℕ} (hp : p.Prime) :
    Norm.norm (zOmegaNormHom s z p) < 1 := by
  have hval : zOmegaNormHom s z p = Norm.norm z * ((p : ℝ) ^ (-s)) := by
    have h := zOmegaNorm_prime_pow s z hp 1
    rw [pow_one, pow_one] at h
    exact h
  have hnn : (0 : ℝ) ≤ Norm.norm z * ((p : ℝ) ^ (-s)) := by positivity
  rw [hval, Real.norm_eq_abs, abs_of_nonneg hnn]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hps : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p : ℝ)),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    gcongr
  have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
  have hinvpos : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
  calc Norm.norm z * ((p : ℝ) ^ (-s)) ≤ Norm.norm z * ((2 : ℝ) ^ (-s)) :=
        mul_le_mul_of_nonneg_left hps hznn
    _ = Norm.norm z * ((2 : ℝ) ^ s)⁻¹ := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    _ < 1 := by
        have hkey := mul_lt_mul_of_pos_right hz hinvpos
        rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey

/-- The Euler factors as an indicator family on all naturals, multipliable. -/
theorem zOmegaNorm_indicator_multipliable (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z < (2 : ℝ) ^ s) :
    Multipliable (Set.mulIndicator {p : ℕ | p.Prime}
      (fun p : ℕ => (1 - Norm.norm z * ((p : ℝ) ^ (-s)))⁻¹)) := by
  rw [← multipliable_subtype_iff_mulIndicator]
  exact zOmega_factors_multipliable s hs z


/-- Pointwise: (1-x)^{-1} <= exp(2x) for 0 <= x <= 1 / 2. -/
theorem inv_one_sub_le_exp (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hone : (0 : ℝ) < 1 - x := by linarith
  have hlog : -Real.log (1 - x) ≤ 2 * x := neg_log_one_sub_le x hx0 hx
  have hkey : Real.log ((1 - x)⁻¹) ≤ 2 * x := by
    rw [Real.log_inv]
    exact hlog
  have hpos : (0 : ℝ) < (1 - x)⁻¹ := inv_pos.mpr hone
  calc (1 - x)⁻¹ = Real.exp (Real.log ((1 - x)⁻¹)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr hkey

/-- Radius version of the p=2 factor bound: ||z|| * 2^(-s) < 1 when ||z|| <= r < 2^s. -/
theorem two_factor_lt_one_radius (s : ℝ) (r : ℝ) (hr0 : 0 ≤ r) (hrs : r < (2 : ℝ) ^ s)
    (z : ℂ) (hz : Norm.norm z ≤ r) :
    Norm.norm z * ((2 : ℝ) ^ (-s)) < 1 := by
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hinv : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
  have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
  rw [hinv]
  have hlt : Norm.norm z < (2 : ℝ) ^ s := lt_of_le_of_lt hz hrs
  have hinvpos : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := inv_pos.mpr h2s
  have hkey := mul_lt_mul_of_pos_right hlt hinvpos
  rwa [mul_inv_cancel₀ (ne_of_gt h2s)] at hkey

/-- Radius version of the p >= 3 half-bound: with ||z|| <= r and
r * 3^(-s) <= 1 / 2, every prime p >= 3 gives ||z|| p^(-s) <= 1 / 2.
Stated alongside the 3 / 2 version so nothing already proven changes. -/
theorem zOmega_half_of_three_le_radius (s : ℝ) (hs0 : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (z : ℂ)
    (hz : Norm.norm z ≤ r) (hrs : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) {p : ℕ} (hp3 : 3 ≤ p) :
    Norm.norm z * ((p : ℝ) ^ (-s)) ≤ 1 / 2 := by
  have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hps : (p : ℝ) ^ (-s) ≤ (3 : ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ (p : ℝ)),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    gcongr
  have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
  calc Norm.norm z * ((p : ℝ) ^ (-s)) ≤ r * ((3 : ℝ) ^ (-s)) := by
        apply mul_le_mul hz hps (by positivity) hr0
    _ ≤ 1 / 2 := hrs

/-- With ||z|| <= 3 / 2 and s > 1, every prime p >= 3 satisfies ||z|| p^(-s) <= 1 / 2. -/
theorem zOmega_half_of_three_le (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hz : Norm.norm z ≤ 3 / 2) {p : ℕ} (hp3 : 3 ≤ p) :
    Norm.norm z * ((p : ℝ) ^ (-s)) ≤ 1 / 2 := by
  have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (p : ℝ) ^ (-s) ≤ (3 : ℝ) ^ (-s) := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ (p : ℝ)),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    gcongr
  have h3s : (3 : ℝ) ^ (-s) ≤ (3 : ℝ) ^ (-(1 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have h3one : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by
    rw [Real.rpow_neg_one]
    norm_num
  have hznn : (0 : ℝ) ≤ Norm.norm z := norm_nonneg z
  calc Norm.norm z * ((p : ℝ) ^ (-s)) ≤ (3 / 2) * ((3 : ℝ) ^ (-s)) := by
        apply mul_le_mul hz hps (by positivity) (by norm_num)
    _ ≤ (3 / 2) * (1 / 3) := by
        rw [←  h3one]
        apply mul_le_mul_of_nonneg_left h3s (by norm_num)
    _ = 1 / 2 := by norm_num

/-- Product monotonicity for nonnegative reals over a finset. -/
theorem finset_prod_le_prod_nonneg {s : Finset ℕ} {f g : ℕ → ℝ}
    (h0 : ∀ i ∈ s, (0 : ℝ) ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : (0 : ℝ) ≤ f a := h0 a (Finset.mem_insert_self a t)
    have hfa : f a ≤ g a := h1 a (Finset.mem_insert_self a t)
    have hrest : ∏ i ∈ t, f i ≤ ∏ i ∈ t, g i := by
      apply ih
      · intro i hi
        exact h0 i (Finset.mem_insert_of_mem hi)
      · intro i hi
        exact h1 i (Finset.mem_insert_of_mem hi)
    have hprodnn : (0 : ℝ) ≤ ∏ i ∈ t, f i := by
      apply Finset.prod_nonneg
      intro i hi
      exact h0 i (Finset.mem_insert_of_mem hi)
    calc f a * ∏ i ∈ t, f i ≤ g a * ∏ i ∈ t, f i :=
          mul_le_mul_of_nonneg_right hfa hprodnn
      _ ≤ g a * ∏ i ∈ t, g i := by
          apply mul_le_mul_of_nonneg_left hrest
          linarith

/-- For a positive real base, cpow is exp of the real log. -/
theorem ofReal_cpow_eq_exp (a : ℝ) (ha : 0 < a) (w : ℂ) :
    ((a : ℝ) : ℂ) ^ w = Complex.exp (w * ((Real.log a : ℝ) : ℂ)) := by
  have hne : ((a : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt ha
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  rw [← Complex.ofReal_log (le_of_lt ha)]
  ring

/-- The manuscript's decomposition: Fbig = (s-1)^(-z) (1 - z / 2^s)^(-1) G2manu.
This is the same F as our cFac form, resplit so that the z-power of the first
factor contributes (-log(s-1))^l / l! -- the form Definition 2.3 consumes. -/
theorem Fbig_eq_manuscript (s : ℝ) (hs : 1 < s) (z : ℂ) :
    Fbig s z = ((s - 1 : ℝ) : ℂ) ^ (-z) * (1 - z / ((2 : ℂ) ^ (s : ℂ)))⁻¹ * G2manu s z := by
  have hc : 0 < cFac s := cFac_pos s hs
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hk : (0 : ℝ) < kappaFac s := kappaFac_pos s hs hc
  unfold Fbig G2manu
  rw [ofReal_cpow_eq_exp (cFac s) hc z, ofReal_cpow_eq_exp (s - 1) hs1 (-z),
    ofReal_cpow_eq_exp (kappaFac s) hk z]
  have hlog : Real.log (kappaFac s) = Real.log (s - 1) + Real.log (cFac s) := by
    unfold kappaFac
    rw [Real.log_mul (ne_of_gt hs1) (ne_of_gt hc)]
  rw [hlog]
  push_cast
  have hkey : Complex.exp (-z * ((Real.log (s - 1) : ℝ) : ℂ))
      * Complex.exp (z * (((Real.log (s - 1) : ℝ) : ℂ) + ((Real.log (cFac s) : ℝ) : ℂ)))
      = Complex.exp (z * ((Real.log (cFac s) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← hkey]
  ring

/-- The manuscript's G2 at s = 1, section 3.2, defined explicitly:
G2(1,z) = 2^(-z) * prod_{p>2} (1 - z/p)^(-1) (1 - 1/p)^z.
NOT obtained as a limit of G2manu: cFac 1 diverges, so kappaFac 1 is a junk
value (0) and G2manu s z at s = 1 would collapse.  Anchors (checked
numerically): G2at1 1 = 1 / 2 (section 1), G2at1 2 = d (equation (1)). -/
noncomputable def G2at1 (z : ℂ) : ℂ :=
  (((1 / 2 : ℝ)) : ℂ) ^ z * G2C 1 z

/-- Manuscript section 3.2: c_i = [z^i] G2(1,z). -/
noncomputable def cCoeff (i : ℕ) : ℂ :=
  iteratedDeriv i G2at1 0 / (Nat.factorial i : ℂ)

/-- MANUSCRIPT section 3.4: the genuine S* = sum_{i>=0} 2^i |c_i|.
SstarConst above is the certified literal 6.9764; this is the object it
approximates.  Connecting them requires the Cauchy tail |c_i| <= M / 4.2^i of
Lemma 3.7, which is a certified arc bound (M = 326) and so a hypothesis. -/
noncomputable def SstarValue : ℝ :=
  ∑' i : ℕ, (2 : ℝ) ^ i * Norm.norm (cCoeff i)

/-- S* converges, given the Cauchy tail bound of Lemma 3.7.
The hypothesis hM is |c_i| <= M / 4.2^i, certified by the 240-interval-arc
evaluation of the manuscript; (2 / 4.2)^i is then summable. -/
theorem SstarValue_summable (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i : ℕ, Norm.norm (cCoeff i) ≤ M / (4.2:ℝ) ^ i) :
    Summable (fun i : ℕ => (2 : ℝ) ^ i * Norm.norm (cCoeff i)) := by
  have hgeom : Summable (fun i : ℕ => M * ((2 : ℝ) / 4.2) ^ i) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply Summable.of_nonneg_of_le _ _ hgeom
  · intro i
    positivity
  · intro i
    have h42 : (0 : ℝ) < (4.2:ℝ) ^ i := by positivity
    have hstep := hM i
    have h2 : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
    calc (2 : ℝ) ^ i * Norm.norm (cCoeff i)
        ≤ (2 : ℝ) ^ i * (M / (4.2:ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt h2)
      _ = M * ((2 : ℝ) / 4.2) ^ i := by
          rw [div_pow]
          field_simp

/-- G2at1 is differentiable on the closed disc of radius 3 / 2.
The cpow factor (1 / 2)^z is entire; G2C 1 . is differentiable on ball 0 2,
which contains closedBall 0 (3 / 2).  Radius 3 / 2 is enough to reach z = 1
(giving sum c_i = 1 / 2); reaching z = 2 would need the radius pushed past 2. -/
theorem G2at1_differentiableOn :
    DifferentiableOn ℂ G2at1 (Metric.closedBall (0 : ℂ) (3 / 2 : ℝ)) := by
  have hsub : Metric.closedBall (0 : ℂ) (3 / 2 : ℝ) ⊆ Metric.ball (0 : ℂ) 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcpow : DifferentiableOn ℂ (fun z : ℂ => (((1 / 2 : ℝ)) : ℂ) ^ z)
      (Metric.closedBall (0 : ℂ) (3 / 2 : ℝ)) := by
    apply Differentiable.differentiableOn
    intro z
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    simp only [ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hG2C : DifferentiableOn ℂ (fun z : ℂ => G2C 1 z)
      (Metric.closedBall (0 : ℂ) (3 / 2 : ℝ)) :=
    (G2C_differentiableOn 1 (le_refl 1)).mono hsub
  unfold G2at1
  exact hcpow.mul hG2C

/-- Wide-radius variant: G2at1 differentiable on closedBall 0 (12 / 5).
Radius 12 / 5 sits inside ball 0 (5 / 2) and strictly contains z = 2, which is
what sum 2^i c_i = d needs. -/
theorem G2at1_differentiableOn_wide :
    DifferentiableOn ℂ G2at1 (Metric.closedBall (0 : ℂ) (12 / 5 : ℝ)) := by
  have hsub : Metric.closedBall (0 : ℂ) (12 / 5 : ℝ) ⊆ Metric.ball (0 : ℂ) (29 / 10) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcpow : DifferentiableOn ℂ (fun z : ℂ => (((1 / 2 : ℝ)) : ℂ) ^ z)
      (Metric.closedBall (0 : ℂ) (12 / 5 : ℝ)) := by
    apply Differentiable.differentiableOn
    intro z
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    simp only [ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hG2C : DifferentiableOn ℂ (fun z : ℂ => G2C 1 z)
      (Metric.closedBall (0 : ℂ) (12 / 5 : ℝ)) :=
    (G2C_differentiableOn_wide 1 (le_refl 1)).mono hsub
  unfold G2at1
  exact hcpow.mul hG2C

/-- MANUSCRIPT section 1: sum_i c_i = 1 / 2.
The series converges at z = 1 (radius 3 / 2 > 1), and G2at1 1 = (1 / 2) G2C(1,1) = 1 / 2. -/
theorem cCoeff_sum : HasSum (fun n : ℕ => cCoeff n) (1 / 2 : ℂ) := by
  have hR : (0 : NNReal) < 3 / 2 := by norm_num
  have hser := G2at1_differentiableOn.hasFPowerSeriesOnBall hR
  have hmem : (1 : ℂ) ∈ Metric.eball (0 : ℂ) ((3 / 2 : NNReal) : ENNReal) := by
    change edist (1 : ℂ) 0 < ((3 / 2 : NNReal) : ENNReal)
    rw [edist_dist, dist_zero_right, norm_one, ENNReal.ofReal_one]
    rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
    rw [ENNReal.coe_lt_coe]
    norm_num
  have hsum := hser.hasSum_sub hmem
  simp only [sub_zero] at hsum
  have hval : G2at1 1 = (1 / 2 : ℂ) := by
    unfold G2at1
    rw [G2C_one_one, mul_one, Complex.cpow_one]
    norm_num
  rw [hval] at hsum
  apply hsum.congr_fun
  intro n
  have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser n
  unfold cCoeff
  rw [hbridge]
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  rfl
/-- S(m) recovered from A_m: Definition 2.3 read backwards. -/
theorem Sm_eq_Am_div (m : ℕ) : Sm m = Am m / 2 ^ m := by
  unfold Am
  have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  field_simp

/-- Manuscript (3): the frozen integral, with g_i(s) replaced by c_i = g_i(1). -/
noncomputable def Ikfrozen (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), cCoeff i * ((Sm (k - i) : ℝ) : ℂ)

/-- MANUSCRIPT LEMMA 2.4 (exactness).  I'_k = sum_i c_i 2^(i-k) A_(k-i).
Every error term downstream is therefore exactly a value of the deterministic
delta, not a bound. -/
theorem Ikfrozen_eq_sum_Am (k : ℕ) :
    Ikfrozen k = ∑ i ∈ Finset.range (k + 1),
      cCoeff i * ((Am (k - i) : ℝ) : ℂ) / (2 : ℂ) ^ (k - i) := by
  unfold Ikfrozen
  apply Finset.sum_congr rfl
  intro i _
  rw [Sm_eq_Am_div]
  push_cast
  ring

/-- Manuscript section 2.3 partial sums and tails.
U_k = sum_{i<=k} i 2^i c_i,  V_k = sum_{i<=k} i^2 2^i c_i,
W_k = sum_{i>k} 2^i c_i,     w_k = sum_{i>k} c_i,
Delta(k) = sum_{i<=k} 2^i c_i delta_{k-i}. -/
noncomputable def Uk (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (i : ℝ) * 2 ^ i * (cCoeff i).re

noncomputable def Vk (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (i : ℝ) ^ 2 * 2 ^ i * (cCoeff i).re

noncomputable def Wk (k : ℕ) : ℝ :=
  ∑' i : ℕ, (if k < i then (2 : ℝ) ^ i * (cCoeff i).re else 0)

noncomputable def wk (k : ℕ) : ℝ :=
  ∑' i : ℕ, (if k < i then (cCoeff i).re else 0)

/-- The signed convolution of section 3.4. -/
noncomputable def DeltaConv (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i * (cCoeff i).re * deltaM (k - i)

/-- D is monotone: m <= k implies D(m) <= D(k). -/
theorem DBound_mono_le (m k : ℕ) (h : m ≤ k) : DBound m ≤ DBound k := by
  unfold DBound
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
  have hm0 : (0:ℝ) ≤ (m : ℝ) := by positivity
  have hlogm : (0:ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.log_nonneg; linarith
  have hlogmk : Real.log ((m : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by linarith)
    linarith
  have hstep : Real.log 2 * (m : ℝ) * Real.log ((m : ℝ) + 1)
      ≤ Real.log 2 * (k : ℝ) * Real.log ((k : ℝ) + 1) := by
    apply mul_le_mul _ hlogmk hlogm (by positivity)
    apply mul_le_mul_of_nonneg_left hmk (le_of_lt hlog2)
  linarith

/-- MANUSCRIPT section 7, the convolution source: |Delta(k)| <= S* D(k).
From Theorem 4.1's |delta_m| <= D(m), the monotonicity of D, and
sum 2^i |c_i| <= S*.  This is what makes Theorem 4.1 load-bearing. -/
theorem deltaConv_le (k : ℕ) (Sstar : ℝ)
    (hdelta : ∀ m : ℕ, |deltaM m| ≤ DBound m)
    (hS : ∑ i ∈ Finset.range (k + 1), (2:ℝ) ^ i * |(cCoeff i).re| ≤ Sstar) :
    |DeltaConv k| ≤ Sstar * DBound k := by
  have hDk0 : (0:ℝ) ≤ DBound k := DBound_nonneg k
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(2:ℝ) ^ i * (cCoeff i).re * deltaM (k - i)|
        ≤ ((2:ℝ) ^ i * |(cCoeff i).re|) * DBound k := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hDle : DBound (k - i) ≤ DBound k := DBound_mono_le (k - i) k (by omega)
    have h2 : (0:ℝ) ≤ (2:ℝ) ^ i := by positivity
    calc |(2:ℝ) ^ i * (cCoeff i).re * deltaM (k - i)|
        = ((2:ℝ) ^ i * |(cCoeff i).re|) * |deltaM (k - i)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h2]
      _ ≤ ((2:ℝ) ^ i * |(cCoeff i).re|) * DBound (k - i) := by
          apply mul_le_mul_of_nonneg_left (hdelta (k - i)) (by positivity)
      _ ≤ ((2:ℝ) ^ i * |(cCoeff i).re|) * DBound k := by
          apply mul_le_mul_of_nonneg_left hDle (by positivity)
  unfold DeltaConv
  calc |∑ i ∈ Finset.range (k + 1), (2:ℝ) ^ i * (cCoeff i).re * deltaM (k - i)|
      ≤ ∑ i ∈ Finset.range (k + 1), |(2:ℝ) ^ i * (cCoeff i).re * deltaM (k - i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), ((2:ℝ) ^ i * |(cCoeff i).re|) * DBound k :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (k + 1), (2:ℝ) ^ i * |(cCoeff i).re|) * DBound k := by
        rw [Finset.sum_mul]
    _ ≤ Sstar * DBound k := mul_le_mul_of_nonneg_right hS hDk0

/-- E(k) defined by f_k = 1 - 2^(-k)(a1 k^2 + E(k)), i.e. solved for E(k). -/
noncomputable def Ek (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (1 - f k) - aOneConst * (k : ℝ) ^ 2

/-- Manuscript (4): the S1 source, D_k = I_k - I'_k.
Ikfrozen is C-valued (built from cCoeff), so take the real part. -/
noncomputable def Dk (k : ℕ) : ℝ := Ik k - (Ikfrozen k).re

/-- Manuscript section 2.3: E1(k) = 2^k D_k. -/
noncomputable def E1k (k : ℕ) : ℝ := (2 : ℝ) ^ k * Dk k

/-- Manuscript section 2.3: the exponentially small source
Eexp(k) = 2^(k+1) w_k - q k^2 W_k - 2^k T_k, with q = log 2 / 4. -/
noncomputable def Eexpk (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (k + 1) * wk k - (Real.log 2 / 4) * (k : ℝ) ^ 2 * Wk k - (2 : ℝ) ^ k * Tk k

/-- Exponential-generating-function form of the binomial theorem:
(x+y)^n / n! = sum_{i+j=n} (x^i/i!)(y^j/j!).
This is the bookkeeping that converts our (log cFac s)^l / l! coefficients into
the manuscript's (-log(s-1))^l / l!, absorbing log kappa into g_i. -/
theorem add_pow_div_factorial (x y : ℂ) (n : ℕ) :
    (x + y) ^ n / (Nat.factorial n : ℂ)
      = ∑ i ∈ Finset.range (n + 1),
          x ^ i / (Nat.factorial i : ℂ) * (y ^ (n - i) / (Nat.factorial (n - i) : ℂ)) := by
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfi : (Nat.factorial i : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hfni : (Nat.factorial (n - i) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  have hfn : (Nat.factorial n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hchoose : ((Nat.choose n i : ℕ) : ℂ) * (Nat.factorial i : ℂ)
      * (Nat.factorial (n - i) : ℂ) = (Nat.factorial n : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  field_simp
  linear_combination (x ^ i * y ^ (n - i)) * hchoose

/-- A1: absolute summability of the z-weighted Dirichlet family. -/
theorem zOmega_summable_radius (s : ℝ) (hs : 1 < s) (r : ℝ) (hr0 : 0 ≤ r)
    (hr3 : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) (hr2 : r < (2 : ℝ) ^ s) (z : ℂ) (hz : ‖z‖ ≤ r) :
    Summable (fun n : ℕ => ‖zOmegaHom s z n‖) := by
  classical
  have hz2 : ‖z‖ < (2 : ℝ) ^ s := lt_of_le_of_lt hz hr2
  set G : ℕ → ℝ := Set.mulIndicator {p : ℕ | p.Prime}
    (fun p : ℕ => (1 - ‖z‖ * ((p : ℝ) ^ (-s)))⁻¹) with hG
  have hGmult : Multipliable G := zOmegaNorm_indicator_multipliable s hs z hz2
  have hGone : ∀ i : ℕ, (1 : ℝ) ≤ G i := by
    intro i
    rw [hG]
    by_cases hp : i ∈ {p : ℕ | p.Prime}
    · rw [Set.mulIndicator_of_mem hp]
      exact zOmega_factor_ge_one s hs z hz2 i hp
    · rw [Set.mulIndicator_of_notMem hp]
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ ‖zOmegaHom s z n‖ := fun n => norm_nonneg _
  apply summable_of_sum_le (c := ((1 - ‖z‖ * ((2 : ℝ) ^ (-s)))⁻¹ * Real.exp (2 * ∑' n : ℕ, ‖z‖ * ((n : ℝ) ^ (-s))))) hnn
  intro u
  set N := u.sup id + 1 with hN
  have hsmooth : ∀ x ∈ u, x ≠ 0 → x ∈ N.smoothNumbers := by
    intro x hxu hx0
    apply mem_smoothNumbers_of_lt N x (Nat.pos_of_ne_zero hx0)
    have : x ≤ u.sup id := Finset.le_sup (f := id) hxu
    omega
  have hgeo := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := (zOmegaNormHom s z).toMonoidHom)
    (fun {p} hp => zOmegaNorm_prime_lt_one s hs z hz2 hp) N
  have hbridge : (∏ p ∈ N.primesBelow, (1 - zOmegaNormHom s z p)⁻¹)
      = ∏ i ∈ Finset.range N, G i := by
    rw [hG]
    have hmi := Finset.prod_mulIndicator_eq_prod_filter (Finset.range N)
      (fun (_ : ℕ) (p : ℕ) => (1 - ‖z‖ * ((p : ℝ) ^ (-s)))⁻¹)
      (fun (_ : ℕ) => ({p : ℕ | p.Prime} : Set ℕ)) (id : ℕ → ℕ)
    simp only [id_eq] at hmi
    rw [hmi]
    rw [Nat.primesBelow]
    apply Finset.prod_congr
    · ext q
      simp [Set.mem_setOf_eq]
    · intro q hq
      simp only [Finset.mem_filter] at hq
      have hqp : q.Prime := hq.2
      have h1 := zOmegaNorm_prime_pow s z hqp 1
      rw [pow_one, pow_one] at h1
      rw [h1]
  have hsm : Summable (fun m : N.smoothNumbers => Norm.norm (zOmegaHom s z m)) := by
    apply hgeo.1.congr
    intro m
    change ‖zOmegaNormHom s z (m : ℕ)‖ = ‖zOmegaHom s z (m : ℕ)‖
    rw [zOmegaNormHom_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hsum_le : (∑ x ∈ u, Norm.norm (zOmegaHom s z x))
      ≤ ∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m) := by
    rw [tsum_subtype (N.smoothNumbers) (fun n : ℕ => Norm.norm (zOmegaHom s z n))]
    have hsm' : Summable (Set.indicator (N.smoothNumbers)
        (fun n : ℕ => Norm.norm (zOmegaHom s z n))) := by
      rwa [←  summable_subtype_iff_indicator]
    have hle : ∀ x ∈ u, Norm.norm (zOmegaHom s z x)
        ≤ Set.indicator (N.smoothNumbers)
          (fun n : ℕ => Norm.norm (zOmegaHom s z n)) x := by
      intro x hxu
      by_cases hx0 : x = 0
      · subst hx0
        rw [show zOmegaHom s z 0 = 0 from map_zero _, norm_zero]
        apply Set.indicator_nonneg
        intro a _
        exact norm_nonneg _
      · rw [Set.indicator_of_mem (hsmooth x hxu hx0)]
    calc ∑ x ∈ u, Norm.norm (zOmegaHom s z x)
        ≤ ∑ x ∈ u, Set.indicator (N.smoothNumbers)
            (fun n : ℕ => Norm.norm (zOmegaHom s z n)) x := Finset.sum_le_sum hle
      _ ≤ ∑' x : ℕ, Set.indicator (N.smoothNumbers)
            (fun n : ℕ => Norm.norm (zOmegaHom s z n)) x := by
          apply hsm'.sum_le_tsum
          intro i _
          apply Set.indicator_nonneg
          intro a _
          exact norm_nonneg _
  have hval : (∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m))
      = ∏ p ∈ N.primesBelow, (1 - zOmegaNormHom s z p)⁻¹ := hgeo.2.tsum_eq
  have hfin : (∏ i ∈ Finset.range N, G i) ≤ ((1 - ‖z‖ * ((2 : ℝ) ^ (-s)))⁻¹ * Real.exp (2 * ∑' n : ℕ, ‖z‖ * ((n : ℝ) ^ (-s)))) := by
    have hprimes_sum : Summable (fun p : Nat.Primes => Norm.norm z * ((p : ℝ) ^ (-s))) :=
      zOmega_prime_sum_summable s hs z
    have hGle : ∀ i ∈ Finset.range N, i ≠ 2 →
        G i ≤ Real.exp (2 * (Norm.norm z * ((i : ℝ) ^ (-s)))) := by
      intro i _ hi2
      rw [hG]
      by_cases hp : i ∈ {p : ℕ | p.Prime}
      · rw [Set.mulIndicator_of_mem hp]
        have hprime : i.Prime := hp
        have hi3 : 3 ≤ i := by
          have h2 : 2 ≤ i := hprime.two_le
          omega
        apply inv_one_sub_le_exp
        · positivity
        · exact zOmega_half_of_three_le_radius s (by linarith) r hr0 z hz hr3 hi3
      · rw [Set.mulIndicator_of_notMem hp]
        have : (0 : ℝ) ≤ 2 * (Norm.norm z * ((i : ℝ) ^ (-s))) := by positivity
        calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
          _ ≤ Real.exp (2 * (Norm.norm z * ((i : ℝ) ^ (-s)))) := Real.exp_le_exp.mpr this
    have hGnn : ∀ i : ℕ, (0 : ℝ) ≤ G i := fun i => le_trans zero_le_one (hGone i)
    by_cases hN2 : 2 ∈ Finset.range N
    · rw [←  Finset.mul_prod_erase (Finset.range N) G hN2]
      have hG2 : G 2 = (1 - Norm.norm z * ((2 : ℝ) ^ (-s)))⁻¹ := by
        rw [hG, Set.mulIndicator_of_mem]
        · norm_num
        · exact Nat.prime_two
      rw [hG2]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (by rw [←  hG2]; exact hGone 2))
      have hsummable_nat : Summable (fun n : ℕ => Norm.norm z * ((n : ℝ) ^ (-s))) := by
        have hb : Summable (fun n : ℕ => ((n : ℝ) ^ (-s))) := by
          rw [Real.summable_nat_rpow]
          linarith
        exact hb.mul_left _
      have hnn_nat : ∀ n : ℕ, (0 : ℝ) ≤ Norm.norm z * ((n : ℝ) ^ (-s)) := by
        intro n
        positivity
      calc ∏ i ∈ (Finset.range N).erase 2, G i
          ≤ ∏ i ∈ (Finset.range N).erase 2,
              Real.exp (2 * (Norm.norm z * ((i : ℝ) ^ (-s)))) := by
            apply finset_prod_le_prod_nonneg
            · intro i _
              exact hGnn i
            · intro i hi
              have hi2 : i ≠ 2 := (Finset.mem_erase.mp hi).1
              have hiN : i ∈ Finset.range N := (Finset.mem_erase.mp hi).2
              exact hGle i hiN hi2
        _ = Real.exp (∑ i ∈ (Finset.range N).erase 2,
              2 * (Norm.norm z * ((i : ℝ) ^ (-s)))) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp (2 * ∑' n : ℕ, Norm.norm z * ((n : ℝ) ^ (-s))) := by
            apply Real.exp_le_exp.mpr
            rw [←  Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            exact hsummable_nat.sum_le_tsum _ (fun i _ => hnn_nat i)
    · have hprod1 : ∏ i ∈ Finset.range N, G i = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_range] at hN2
        have hnp : i ∉ {p : ℕ | p.Prime} := by
          simp only [Set.mem_setOf_eq]
          intro hprime
          have := hprime.two_le
          omega
        rw [hG, Set.mulIndicator_of_notMem hnp]
      rw [hprod1]
      have hx34 : Norm.norm z * ((2 : ℝ) ^ (-s)) < 1 :=
        two_factor_lt_one_radius s r hr0 hr2 z hz
      have hxnn : (0 : ℝ) ≤ Norm.norm z * ((2 : ℝ) ^ (-s)) := by positivity
      have hinv1 : (1 : ℝ) ≤ (1 - Norm.norm z * ((2 : ℝ) ^ (-s)))⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) (by linarith)]
        linarith
      have hexp1 : (1 : ℝ) ≤ Real.exp (2 * ∑' n : ℕ, Norm.norm z * ((n : ℝ) ^ (-s))) := by
        rw [Real.one_le_exp_iff]
        have hsummable_nat : Summable (fun n : ℕ => Norm.norm z * ((n : ℝ) ^ (-s))) := by
          have hb : Summable (fun n : ℕ => ((n : ℝ) ^ (-s))) := by
            rw [Real.summable_nat_rpow]
            linarith
          exact hb.mul_left _
        have : (0 : ℝ) ≤ ∑' n : ℕ, Norm.norm z * ((n : ℝ) ^ (-s)) := by
          apply tsum_nonneg
          intro n
          positivity
        linarith
      nlinarith [hinv1, hexp1]
  calc (∑ x ∈ u, Norm.norm (zOmegaHom s z x))
      ≤ ∑' m : N.smoothNumbers, Norm.norm (zOmegaHom s z m) := hsum_le
    _ = ∏ p ∈ N.primesBelow, (1 - zOmegaNormHom s z p)⁻¹ := hval
    _ = ∏ i ∈ Finset.range N, G i := hbridge
    _ ≤ ((1 - ‖z‖ * ((2 : ℝ) ^ (-s)))⁻¹ * Real.exp (2 * ∑' n : ℕ, ‖z‖ * ((n : ℝ) ^ (-s)))) := hfin

/-- A1 at radius 3 / 2 (the form Lemma 2.2 uses). -/
theorem zOmega_summable (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3 / 2) :
    Summable (fun n : ℕ => Norm.norm (zOmegaHom s z n)) := by
  apply zOmega_summable_radius s hs (3 / 2) (by norm_num) _ _ z hz
  · have h3 : (3 : ℝ) ^ (-s) ≤ (3 : ℝ) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    have h3one : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by
      rw [Real.rpow_neg_one]
      norm_num
    rw [h3one] at h3
    linarith
  · have h2 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ s := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rw [Real.rpow_one] at h2
    linarith

/-- A2: the Euler product for the z-weighted family. -/
theorem zOmega_eulerProduct (s : ℝ) (hs : 1 < s) (z : ℂ)
    (hsum : Summable (fun n : ℕ => ‖zOmegaHom s z n‖)) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹) = ∑' n : ℕ, zOmegaHom s z n :=
  (EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq

/-!
### A3 scaffold: the Euler product equals Fbig

The identity (verified numerically to 12+ digits):
  prod_p (1 - z p^-s)^-1  =  (cFac s)^z * (1 - z 2^-s)^-1 * G2C s z

with cFac s = prod_{p>=3} (1 - p^-s)^-1 and
G2C s z = prod_{p>=3} (1 - z p^-s)^-1 (1 - p^-s)^z.

MATHLIB GAP: neither log-of-tprod nor cpow-of-tprod exists in this pin,
so B1 below must be built.  Route: multipliability + positivity gives
HasProd, and log is continuous, so log of the limit is the limit of the
log partial sums.

Sub-obligations:

B1  log_tprod_real : for a multipliable family of positive reals,
    log (prod' f) = sum' (log o f).           [THE MATHLIB GAP]

B2  cFac_cpow : (cFac s : C)^z = exp (z * sum'_{p>=3} log ((1 - p^-s)^-1)).
    From B1 and the definition of cpow for a positive real base.

B3  tail_regroup : prod'_{p>=3} (1 - z p^-s)^-1
      = (cFac s)^z * G2C s z,
    i.e. the regularising factors telescope.  Uses B2 and multipliability
    of both tail families.

B4  split_two : prod'_p (1 - z p^-s)^-1
      = (1 - z 2^-s)^-1 * prod'_{p>=3} (1 - z p^-s)^-1.
    Splitting the prime tprod at p = 2.

A3 follows from B3 and B4 by unfolding Fbig.
-/

/-- B1: log of an infinite product of positives is the sum of logs. -/
theorem log_tprod_real {ι : Type*} {f : ι → ℝ} (hpos : ∀ i, 0 < f i)
    (hmul : Multipliable f) (hlog : Summable (fun i => Real.log (f i))) :
    Real.log (∏' i : ι, f i) = ∑' i : ι, Real.log (f i) := by
  have hpart : ∀ t : Finset ι, ∏ i ∈ t, f i
      = Real.exp (∑ i ∈ t, Real.log (f i)) := by
    intro t
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.exp_log (hpos i)]
  have h1 : HasProd f (∏' i : ι, f i) := hmul.hasProd
  have h2 : HasSum (fun i => Real.log (f i)) (∑' i : ι, Real.log (f i)) := hlog.hasSum
  have h3 : HasProd f (Real.exp (∑' i : ι, Real.log (f i))) := by
    have hcomp := (Real.continuous_exp.tendsto _).comp h2
    apply hcomp.congr
    intro t
    rw [Function.comp_apply, ←  hpart t]
  have heq : (∏' i : ι, f i) = Real.exp (∑' i : ι, Real.log (f i)) :=
    h1.unique h3
  rw [heq, Real.log_exp]

/-- B2: the cFac factor as an exponential. -/
theorem cFac_cpow (s : ℝ) (hc : 0 < cFac s) (z : ℂ) :
    ((cFac s : ℝ) : ℂ) ^ z
      = Complex.exp (z * ((Real.log (cFac s) : ℝ) : ℂ)) := by
  have hne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hc
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  rw [←  Complex.ofReal_log (le_of_lt hc)]
  ring

/-- A prime p with 3 <= p and p != 3 satisfies 5 <= p (4 is not prime). -/
theorem five_le_of_prime_ne_three {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (hne : p ≠ 3) :
    5 ≤ p := by
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p
    · exact absurd rfl hne
    · exact absurd hp (by norm_num)
  · exact h

/-- Primes >= 3 excluding 3 correspond to primes >= 5. -/
def primesGE3_ne_equiv :
    {q : {p : ℕ // p.Prime ∧ 3 ≤ p} // q.1 ≠ 3} ≃ {p : ℕ // p.Prime ∧ 5 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2.1,
    five_le_of_prime_ne_three q.1.2.1 q.1.2.2 q.2 ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1, by have h5 := r.2.2; omega ⟩, by
    have h5 := r.2.2
    simp only [ne_eq]
    omega ⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl

/-- The complement of {b3} in the p >= 3 primes is equivalent to the p >= 5 primes. -/
def compl_b3_equiv :
    (({⟨ 3, Nat.prime_three, le_refl 3 ⟩} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ :
      Set {p : ℕ // p.Prime ∧ 3 ≤ p}) ≃ {p : ℕ // p.Prime ∧ 5 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2.1, by
    have hne : q.1.1 ≠ 3 := by
      intro h
      apply q.2
      apply Subtype.ext
      exact h
    exact five_le_of_prime_ne_three q.1.2.1 q.1.2.2 hne ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1, by have := r.2.2; omega ⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h5 := r.2.2
    have : r.1 = 3 := congrArg Subtype.val h
    omega ⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl

/-- If the p >= 5 tail is multipliable, so is the p >= 3 family, and the
product splits off the p = 3 factor. -/
theorem tprod_split_three {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    [ContinuousMul M] (f : ℕ → M)
    (hf5 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => f p)
      ∧ (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, f p)
        = f 3 * ∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p := by
  classical
  set b3 : {p : ℕ // p.Prime ∧ 3 ≤ p} := ⟨ 3, Nat.prime_three, le_refl 3 ⟩ with hb3
  set g : {p : ℕ // p.Prime ∧ 3 ≤ p} → M := fun p => f p with hg
  have hsingle : HasProd ((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p}).restrict g)) (g b3) := by
    have := hasProd_singleton b3 g
    exact this
  have hcompl : HasProd (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := by
    have hbase : HasProd (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => f p)
        (∏' p : {p : ℕ // p.Prime ∧ 5 ≤ p}, f p) := hf5.hasProd
    exact (compl_b3_equiv.hasProd_iff).mpr hbase
  have hequiv : Multipliable (((({b3} : Set {p : ℕ // p.Prime ∧ 3 ≤ p})ᶜ).restrict g)) :=
    hcompl.multipliable
  have hall := hsingle.mul_compl hcompl
  refine ⟨ hall.multipliable, ?_⟩
  rw [hall.tprod_eq]

theorem reg_factors_tprod (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hc : 0 < cFac s)
    (hmul : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hpos : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlog : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    ((cFac s : ℝ) : ℂ) ^ z
      = Complex.exp (z * ((∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹) : ℝ) : ℂ)) := by
  rw [cFac_cpow s hc z]
  congr 2
  have hlogeq : Real.log (cFac s)
      = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹) := by
    unfold cFac
    exact log_tprod_real hpos hmul hlog
  rw [hlogeq]

/-- The regularised family is multipliable over p >= 3: adjoin the single
p = 3 factor to the p >= 5 tail (the p=3 exp-log BOUND fails, but the single
extra factor is harmless). -/
theorem reg_multipliable_three (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
        * (((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) := by
  have h5 := prime_factor_multipliable_complex s hs z hz
  have hsplit := tprod_split_three
    (fun n : ℕ => (1 - z * (((n : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      * (((1 - (n : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) h5
  exact hsplit.1

/-- D2: the regularised family at z = 2, s = 1 is multipliable.
Immediate from reg_multipliable_three, since ||(2:C)|| = 2 <= 2. -/
theorem reg_multipliable_three_at_two :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - (2 : ℂ) * ((((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ))⁻¹
        * (((1 - ((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)) ^ (2 : ℂ)) := by
  have h := reg_multipliable_three 1 (le_refl 1) 2 (by norm_num)
  exact h

/-- D3: the complex p >= 3 product at z = 2 is the cast of the real one. -/
theorem G2C_at_two_ofReal :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - (2 : ℂ) * ((((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ))⁻¹
          * (((1 - ((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)) ^ (2 : ℂ))
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
          (((((1 - 2 * ((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ))⁻¹
            * ((1 - ((p : ℕ):ℝ) ^ (-(1 : ℝ)) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
  apply tprod_congr
  intro p
  have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
  have hle : ((p : ℕ):ℝ) ^ (-(1 : ℝ)) ≤ 1 / 3 := by
    rw [Real.rpow_neg_one]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hpos : (0 : ℝ) < ((p : ℕ):ℝ) ^ (-(1 : ℝ)) := by positivity
  have hne : (1 : ℝ) - 2 * (((p : ℕ):ℝ) ^ (-(1 : ℝ))) ≠ 0 := by
    have : 2 * (((p : ℕ):ℝ) ^ (-(1 : ℝ))) ≤ 2 / 3 := by linarith
    intro hcon
    linarith
  exact reg_factor_at_two (((p : ℕ):ℝ) ^ (-(1 : ℝ))) hne

/-- Bound on the correction for the (1 - p^-s)^(-z) family. -/
theorem cpow_neg_sub_one_bound (p : ℕ) (hp : 5 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm ((((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z) - 1)
      ≤ 8 * (((p : ℕ):ℝ) ^ (-s)) := by
  have hp3R : (5 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < ((p : ℕ):ℝ) := by linarith
  set a : ℝ := ((p : ℕ):ℝ) ^ (-s) with ha
  have hapos : (0 : ℝ) < a := by rw [ha]; positivity
  have hale : a ≤ 1 / 5 := by
    rw [ha]
    have h1 : ((p : ℕ):ℝ) ^ (-s) ≤ ((p : ℕ):ℝ) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    have h2 : ((p : ℕ):ℝ) ^ (-(1 : ℝ)) = 1 / ((p : ℕ):ℝ) := by
      rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [h2] at h1
    have h3 : (1 : ℝ) / ((p : ℕ):ℝ) ≤ 1 / 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3R
    linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hlogbound : Norm.norm (Real.log (1 - a)) ≤ 2 * a := by
    rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
    exact neg_log_one_sub_le a hapos.le (by linarith)
  have hane : (((1 - a : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hcpow : (((1 - a : ℝ)) : ℂ) ^ (-z)
      = Complex.exp ((-z) * ((Real.log (1 - a) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hane, ←  Complex.ofReal_log h1a.le]
    ring_nf
  set c : ℂ := (-z) * ((Real.log (1 - a) : ℝ) : ℂ) with hc
  have hcnorm : Norm.norm c ≤ 4 * a := by
    rw [hc, norm_mul, norm_neg, Complex.norm_real]
    calc Norm.norm z * Norm.norm (Real.log (1 - a)) ≤ 2 * (2 * a) := by
          apply mul_le_mul hz hlogbound (norm_nonneg _) (by norm_num)
      _ = 4 * a := by ring
  have hc1 : Norm.norm c ≤ 1 := by
    have : (4 : ℝ) * a ≤ 4 * (1 / 5) := by
      apply mul_le_mul_of_nonneg_left hale (by norm_num)
    linarith
  rw [hcpow]
  calc Norm.norm (Complex.exp c - 1) ≤ 2 * Norm.norm c := Complex.norm_exp_sub_one_le hc1
    _ ≤ 2 * (4 * a) := by linarith
    _ = 8 * a := by ring

/-- Summability of the correction for the (1 - p^-s)^(-z) family, p >= 5. -/
theorem cpow_neg_sub_one_summable (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      Norm.norm ((((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z) - 1)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => 8 * (((p : ℕ):ℝ) ^ (-s))) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-s))) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => (((p : ℕ):ℝ) ^ (-s))) :=
      hbase.subtype _
    exact hsub.mul_left 8
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      cpow_neg_sub_one_bound (p : ℕ) p.property.2 s (le_of_lt hs) z hz)
    hcomp

theorem cpow_neg_multipliable_five (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z)) := by
  have hsum := cpow_neg_sub_one_summable s hs z hz
  have hmult : Multipliable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      1 + ((((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z) - 1)) := by
    apply Complex.multipliable_one_add_of_summable
    exact hsum.of_norm
  apply hmult.congr
  intro p
  ring

/-- The family (1 - p^-s)^(-z) is multipliable over primes >= 3. -/
theorem cpow_neg_multipliable_three (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z)) := by
  have h5 := cpow_neg_multipliable_five s hs z hz
  have hsplit := tprod_split_three
    (fun n : ℕ => (((1 - (n : ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z)) h5
  exact hsplit.1

/-- Pointwise factorisation: the plain Euler factor splits into the
cpow-negative factor times the regularised factor. -/
theorem euler_factor_split (a : ℝ) (ha : 0 < 1 - a) (z w : ℂ) :
    (1 - w)⁻¹ = ((((1 - a : ℝ)) : ℂ)) ^ (-z)
      * ((1 - w)⁻¹ * (((1 - a : ℝ)) : ℂ) ^ z) := by
  have hane : (((1 - a : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hpow : (((1 - a : ℝ)) : ℂ) ^ z ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro hcon
    exact hane hcon.1
  rw [Complex.cpow_neg]
  field_simp

/-- Exponentiating a HasSum gives a HasProd (complex, with a scalar factor). -/
theorem hasProd_cexp_of_hasSum {ι : Type*} {f : ι → ℂ} {a c : ℂ}
    (h : HasSum f a) :
    HasProd (fun i => Complex.exp (c * f i)) (Complex.exp (c * a)) := by
  have hmul : HasSum (fun i => c * f i) (c * a) := h.mul_left c
  have hcont := (Complex.continuous_exp.tendsto (c * a)).comp hmul
  apply hcont.congr
  intro t
  rw [Function.comp_apply, Complex.exp_sum]

/-- The cpow-negative product equals cFac^z. Bridges the complex product to
the real log-sum via reg_factors_tprod. -/
theorem cpow_neg_tprod_eq_cFac (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        (((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ (-z))
      (((cFac s : ℝ) : ℂ) ^ z) := by
  have hsumR : HasSum (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)) (Real.log (cFac s)) := by
    have hlogeq : Real.log (cFac s)
        = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
            Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹) := by
      unfold cFac
      exact log_tprod_real hposR hmulR hlogR
    rw [hlogeq]
    exact hlogR.hasSum
  have hsumC : HasSum (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      ((Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹) : ℝ) : ℂ))
      ((Real.log (cFac s) : ℝ) : ℂ) := by
    have h := hsumR.ofReal
    apply h.congr
    intro t
    rw [Complex.ofReal_sum]
  have hbridge := hasProd_cexp_of_hasSum (c := z) hsumC
  rw [cFac_cpow s hc z]
  apply hbridge.congr_fun
  intro p
  have hpos : (0 : ℝ) < 1 - ((p : ℕ):ℝ) ^ (-s) := hposR p |> inv_pos.mp
  have hane : (((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  rw [Complex.cpow_def_of_ne_zero hane, ←  Complex.ofReal_log hpos.le]
  congr 1
  rw [Real.log_inv]
  push_cast
  ring

/-- The regularised product over p >= 3 is exactly G2C. -/
theorem reg_tprod_eq_G2C (s : ℝ) (hs : 1 ≤ s) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
          * (((1 - ((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ^ z)
      = G2C s z := by
  have h5 := prime_factor_multipliable_complex s hs z hz
  have hsplit := tprod_split_three
    (fun n : ℕ => (1 - z * (((n : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹
      * (((1 - (n : ℝ) ^ (-s) : ℝ) : ℂ)) ^ z) h5
  rw [hsplit.2]
  unfold G2C G2tailC
  norm_num

/-- D5 (manuscript section 1): G2(1,2) = d.
Function-value half of "sum 2^i c_i = d". -/
theorem G2at1_two_eq_dConst : G2at1 2 = ((dConst : ℝ) : ℂ) := by
  have hreg := reg_tprod_eq_G2C 1 (le_refl 1) 2 (by norm_num)
  unfold G2at1
  rw [← hreg, G2C_at_two_ofReal]
  have hspell : (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      ((((1 - 2 * ((p : ℕ) : ℝ) ^ (-(1 : ℝ)))⁻¹
        * (1 - ((p : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2 : ℝ)) : ℂ))
      = ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        ((((1 - 2 / ((p : ℕ) : ℝ))⁻¹ * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
    apply tprod_congr
    intro p
    congr 2
    · rw [Real.rpow_neg_one]
      ring_nf
    · rw [Real.rpow_neg_one]
      ring_nf
  rw [hspell, dConst_prod_ofReal]
  unfold dConst
  rw [dConst_prod_eq_subtype]
  push_cast
  norm_num

/-- MANUSCRIPT section 1: sum_i c_i 2^i = d.
The series converges at z = 2 (radius 12 / 5 > 2, from the wide-radius chain),
and G2at1 2 = d by D5. -/
theorem cCoeff_two_pow_sum :
    HasSum (fun n : ℕ => cCoeff n * (2 : ℂ) ^ n) ((dConst : ℝ) : ℂ) := by
  have hR : (0 : NNReal) < 12 / 5 := by norm_num
  have hser := G2at1_differentiableOn_wide.hasFPowerSeriesOnBall hR
  have hmem : (2 : ℂ) ∈ Metric.eball (0 : ℂ) ((12 / 5 : NNReal) : ENNReal) := by
    change edist (2 : ℂ) 0 < ((12 / 5 : NNReal) : ENNReal)
    rw [edist_dist, dist_zero_right]
    rw [show Norm.norm (2 : ℂ) = (2 : ℝ) by norm_num]
    rw [show ENNReal.ofReal (2 : ℝ) = ((2 : NNReal) : ENNReal) by
      simp [ENNReal.ofReal]]
    rw [ENNReal.coe_lt_coe]
    norm_num
  have hsum := hser.hasSum_sub hmem
  simp only [sub_zero] at hsum
  rw [G2at1_two_eq_dConst] at hsum
  apply hsum.congr_fun
  intro n
  have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser n
  unfold cCoeff
  rw [hbridge]
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [mul_comm]

/-- Real form of the first coefficient identity: sum (c_i).re = 1 / 2. -/
theorem cCoeff_re_sum : HasSum (fun i : ℕ => (cCoeff i).re) (1 / 2 : ℝ) := by
  have h := Complex.hasSum_re cCoeff_sum
  simpa using h

/-- Real form of the second: sum 2^i (c_i).re = d. -/
theorem cCoeff_re_two_pow_sum :
    HasSum (fun i : ℕ => (2 : ℝ) ^ i * (cCoeff i).re) dConst := by
  have h := Complex.hasSum_re cCoeff_two_pow_sum
  simp only [Complex.ofReal_re] at h
  apply h.congr_fun
  intro i
  rw [Complex.mul_re]
  have h2 : ((2 : ℂ) ^ i).im = 0 := by
    rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  have h2r : ((2 : ℂ) ^ i).re = (2 : ℝ) ^ i := by
    rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  rw [h2, h2r]
  ring

/-- For a summable family, the partial sum over range (k+1) is the total minus
the indicator tail.  Turns the manuscript's w_k and W_k (defined as indicator
tails) into partial sums of the coefficient identities. -/
theorem sum_range_eq_total_sub_tail {f : ℕ → ℝ} {S : ℝ}
    (hf : HasSum f S) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), f i
      = S - ∑' i : ℕ, (if k < i then f i else 0) := by
  classical
  have hfin : HasSum (fun i : ℕ => if i ∈ Finset.range (k+1) then f i else 0)
      (∑ i ∈ Finset.range (k + 1), f i) := by
    have h0 : HasSum (fun i : ℕ => if i ∈ Finset.range (k+1) then f i else 0)
        (∑ i ∈ Finset.range (k+1), (if i ∈ Finset.range (k+1) then f i else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro i hi
      rw [if_neg hi]
    rwa [Finset.sum_congr rfl (fun i hi => if_pos hi)] at h0
  have hdiff := hf.sub hfin
  have heq : (fun i : ℕ => f i - (if i ∈ Finset.range (k+1) then f i else 0))
      = fun i : ℕ => (if k < i then f i else 0) := by
    funext i
    by_cases h : i ∈ Finset.range (k+1)
    · rw [if_pos h, if_neg (by simp only [Finset.mem_range] at h; omega)]
      ring
    · rw [if_neg h, if_pos (by simp only [Finset.mem_range] at h; omega)]
      ring
  rw [heq] at hdiff
  rw [hdiff.tsum_eq]
  ring

/-- Partial sums of the c_i: manuscript section 2.3's w_k is the tail. -/
theorem cCoeff_partial_sum (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (cCoeff i).re = 1 / 2 - wk k := by
  unfold wk
  exact sum_range_eq_total_sub_tail cCoeff_re_sum k

/-- Partial sums of 2^i c_i: W_k is the tail. -/
theorem cCoeff_two_pow_partial_sum (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i * (cCoeff i).re = dConst - Wk k := by
  unfold Wk
  exact sum_range_eq_total_sub_tail cCoeff_re_two_pow_sum k

/-- Definition 2.3 read as a formula for A_m in terms of delta_m. -/
theorem Am_eq_delta (m : ℕ) :
    Am m = (2 : ℝ) ^ (m + 1) - (Real.log 2 / 4) * (m : ℝ) ^ 2 + deltaM m := by
  unfold deltaM
  ring

/-- Per-term expansion for the frozen integral, for i <= k. -/
theorem Ikfrozen_term (k i : ℕ) (hi : i ≤ k) :
    (cCoeff i).re * Sm (k - i)
      = 2 * (cCoeff i).re
        - (Real.log 2 / 4) * ((2 : ℝ)^i * (cCoeff i).re * ((k : ℝ) - (i : ℝ))^2) / (2 : ℝ)^k
        + ((2 : ℝ)^i * (cCoeff i).re * deltaM (k - i)) / (2 : ℝ)^k := by
  have hpow : (2 : ℝ)^(k-i) * (2 : ℝ)^i = (2 : ℝ)^k := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - (i : ℝ) := Nat.cast_sub hi
  have h1 : ((2 : ℝ)^(k-i)) ≠ 0 := by positivity
  have h2 : ((2 : ℝ)^i) ≠ 0 := by positivity
  rw [Sm_eq_Am_div, Am_eq_delta, hcast, ← hpow]
  field_simp
  ring

/-- The real part of the frozen integral distributes over the sum, and each
term's real part is (c_i).re * S(k-i) since S is real. -/
theorem Ikfrozen_re_eq (k : ℕ) :
    (Ikfrozen k).re = ∑ i ∈ Finset.range (k + 1), (cCoeff i).re * Sm (k - i) := by
  unfold Ikfrozen
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Expanding (k-i)^2 under the sum: the quadratic weight splits into the
three partial sums of section 2.3. -/
theorem sum_two_pow_sq_expand (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        (2 : ℝ)^i * (cCoeff i).re * ((k : ℝ) - (i : ℝ))^2
      = (k : ℝ)^2 * (dConst - Wk k) - 2 * (k : ℝ) * Uk k + Vk k := by
  have hexp : ∀ i ∈ Finset.range (k + 1),
      (2 : ℝ)^i * (cCoeff i).re * ((k : ℝ) - (i : ℝ))^2
        = (k : ℝ)^2 * ((2 : ℝ)^i * (cCoeff i).re)
          - 2 * (k : ℝ) * ((i : ℝ) * (2 : ℝ)^i * (cCoeff i).re)
          + ((i : ℝ)^2 * (2 : ℝ)^i * (cCoeff i).re) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [cCoeff_two_pow_partial_sum]
  unfold Uk Vk
  ring

theorem Ikfrozen_re_expand (k : ℕ) :
    (Ikfrozen k).re
      = 2 * (1 / 2 - wk k)
        - (Real.log 2 / 4)
            * ((k : ℝ)^2 * (dConst - Wk k) - 2 * (k : ℝ) * Uk k + Vk k) / (2 : ℝ) ^ k
        + DeltaConv k / (2 : ℝ) ^ k := by
  rw [Ikfrozen_re_eq]
  rw [Finset.sum_congr rfl (fun i hi => Ikfrozen_term k i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · rw [← Finset.mul_sum, cCoeff_partial_sum]
    · rw [← Finset.sum_div, ← Finset.mul_sum]
      congr 2
      exact sum_two_pow_sq_expand k
  · rw [← Finset.sum_div]
    unfold DeltaConv
    rfl

/-- B3 (HasProd form): the p >= 3 family has the factored value.
Stated with HasProd rather than tprod because HasProd composes with
mul_compl and Equiv.hasProd_iff, which tprod does not. -/
theorem tail_regroup_hasProd (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
        (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      (((cFac s : ℝ) : ℂ) ^ z * G2C s z) := by
  have hcpow := cpow_neg_tprod_eq_cFac s hs z hz hc hmulR hposR hlogR
  have hreg := (reg_multipliable_three s (le_of_lt hs) z hz).hasProd
  have hmul := hcpow.mul hreg
  rw [reg_tprod_eq_G2C s (le_of_lt hs) z hz] at hmul
  apply hmul.congr_fun
  intro p
  have hpos : (0 : ℝ) < 1 - ((p : ℕ):ℝ) ^ (-s) := hposR p |> inv_pos.mp
  exact euler_factor_split (((p : ℕ):ℝ) ^ (-s)) hpos z (z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))

/-- B3: the p >= 3 tail regroups into cFac^z times G2C. -/
theorem tail_regroup (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3 / 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = ((cFac s : ℝ) : ℂ) ^ z * G2C s z :=
  (tail_regroup_hasProd s hs z (by linarith) hc hmulR hposR hlogR).tprod_eq

/-- A prime p with p != 2 satisfies 3 <= p. -/
theorem three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- The complement of {2} in the primes corresponds to the primes >= 3. -/
def compl_two_equiv :
    (({⟨ 2, Nat.prime_two ⟩} : Set {p : ℕ // p.Prime})ᶜ : Set {p : ℕ // p.Prime})
      ≃ {p : ℕ // p.Prime ∧ 3 ≤ p} where
  toFun q := ⟨ q.1.1, q.1.2, by
    have hne : q.1.1 ≠ 2 := by
      intro h
      apply q.2
      apply Subtype.ext
      exact h
    exact three_le_of_prime_ne_two q.1.2 hne ⟩
  invFun r := ⟨ ⟨ r.1, r.2.1 ⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h3 := r.2.2
    have : r.1 = 2 := congrArg Subtype.val h
    omega ⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro r
    apply Subtype.ext
    rfl

/-- Splitting a product over all primes into p = 2 and the p >= 3 tail. -/
theorem tprod_split_two {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    [ContinuousMul M] (f : ℕ → M)
    (hf3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => f p)) :
    Multipliable (fun p : {p : ℕ // p.Prime} => f p)
      ∧ (∏' p : {p : ℕ // p.Prime}, f p)
        = f 2 * ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, f p := by
  classical
  set b2 : {p : ℕ // p.Prime} := ⟨ 2, Nat.prime_two ⟩ with hb2
  set g : {p : ℕ // p.Prime} → M := fun p => f p with hg
  have hsingle : HasProd ((({b2} : Set {p : ℕ // p.Prime}).restrict g)) (g b2) :=
    hasProd_singleton b2 g
  have hcompl : HasProd (((({b2} : Set {p : ℕ // p.Prime})ᶜ).restrict g))
      (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, f p) :=
    (compl_two_equiv.hasProd_iff).mpr hf3.hasProd
  have hall := hsingle.mul_compl hcompl
  exact ⟨ hall.multipliable, hall.tprod_eq ⟩

/-- cFac s = zeta(s) * (1 - 2^(-s)) for s > 1. -/
theorem cFac_eq_zeta (s : ℝ) (hs : 1 < s) :
    ((cFac s : ℝ) : ℂ)
      = riemannZeta (s : ℂ) * (1 - ((2 : ℂ)) ^ (-(s : ℂ))) := by
  have hzeta := zeta_split_probe s hs
  have hsplit := (tprod_split_two
    (fun n : ℕ => (1 - (((n : ℕ):ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹)
    (cFac_multipliable_complex s hs)).2
  rw [hzeta, ← cFac_ofReal s hs] at hsplit
  have hcast : (((2 : ℕ):ℝ) : ℂ) = ((2 : ℂ)) := by norm_num
  rw [hcast] at hsplit
  have hne := two_factor_ne_one s hs
  rw [hsplit]
  field_simp

/-- The residue, restricted to the right half-plane (where our real s lives). -/
theorem zeta_residue_halfplane :
    Filter.Tendsto (fun z : ℂ => (z - 1) * riemannZeta z)
      (nhdsWithin 1 {z : ℂ | 1 < z.re}) (nhds 1) := by
  apply Filter.Tendsto.mono_left riemannZeta_residue_one
  apply nhdsWithin_mono
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcon
  rw [hcon] at hz
  simp at hz

/-- The coercion carries real s -> 1+ into the complex right half-plane at 1. -/
theorem ofReal_tendsto_halfplane :
    Filter.Tendsto (fun s : ℝ => (s : ℂ))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhdsWithin 1 {z : ℂ | 1 < z.re}) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hcont : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhds 1) (nhds ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1)
    simpa using hcont.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Complex.ofReal_re]
    exact hs

/-- kappa(s) = (s-1) cFac s tends to 1 / 2 as s -> 1 from above.
This is the limit that section 3.5's mean value step needs, and the reason
G2(1,z) = 2^(-z) prod_{p>2}(...) has the 2^(-z) prefactor. -/
theorem kappaFac_tendsto_half :
    Filter.Tendsto kappaFac (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (1 / 2 : ℝ)) := by
  rw [← Filter.tendsto_ofReal_iff]
  have hres : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds 1) :=
    zeta_residue_halfplane.comp ofReal_tendsto_halfplane
  have htwo : Filter.Tendsto (fun s : ℝ => 1 - ((2 : ℂ)) ^ (-(s : ℂ)))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (1 / 2 : ℂ)) := by
    have hcont : ContinuousAt (fun s : ℝ => 1 - ((2 : ℂ)) ^ (-(s : ℂ))) 1 := by
      apply ContinuousAt.sub continuousAt_const
      apply ContinuousAt.const_cpow
      · exact (Complex.continuous_ofReal.continuousAt).neg
      · left; norm_num
    have hval : (fun s : ℝ => 1 - ((2 : ℂ)) ^ (-(s : ℂ))) 1 = (1 / 2 : ℂ) := by
      have hkey : ((2 : ℂ)) ^ (-(((1 : ℝ)) : ℂ)) = (((2 : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) := by
        rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) by norm_num,
          show (-(((1 : ℝ)) : ℂ)) = (((-1 : ℝ)) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      change (1 : ℂ) - ((2 : ℂ)) ^ (-(((1 : ℝ)) : ℂ)) = (1 / 2 : ℂ)
      rw [hkey, Real.rpow_neg_one]
      norm_num
    rw [← hval]
    exact hcont.continuousWithinAt
  have hprod := hres.mul htwo
  simp only [one_mul] at hprod
  rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num]
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  unfold kappaFac
  push_cast
  rw [cFac_eq_zeta s hs1]
  ring

/-- At a prime, the z-weighted hom is just z * p^(-s). -/
theorem zOmegaHom_prime (s : ℝ) (z : ℂ) {p : ℕ} (hp : p.Prime) :
    zOmegaHom s z p = z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ) := by
  have hp0 : (p : ℕ) ≠ 0 := hp.pos.ne'
  change (if (p : ℕ) = 0 then 0
    else z ^ (bigOmega (p : ℕ)) * (((p : ℕ) : ℂ) ^ (-(s : ℂ)))) = _
  rw [if_neg hp0]
  have hO : bigOmega (p : ℕ) = 1 := by
    have := bigOmega_prime_pow hp 1
    rwa [pow_one] at this
  rw [hO, pow_one]
  congr 1
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg p)]

/-- B4: split the prime product at p = 2. -/
theorem split_two (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3 / 2)
    (hmul3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹)
      = (1 - z * (((2 : ℕ):ℝ) ^ (-s) : ℝ))⁻¹
        * ∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p}, (1 - z * (((p : ℕ):ℝ) ^ (-s) : ℝ))⁻¹ := by
  have hcongr : (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹)
      = ∏' p : {p : ℕ // p.Prime}, (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    apply tprod_congr
    intro p
    rw [zOmegaHom_prime s z p.2]
  rw [hcongr]
  have hsplit := tprod_split_two
    (fun n : ℕ => (1 - z * (((n : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) hmul3
  rw [hsplit.2]

/-- A3: the Euler product equals the factored form Fbig. -/
theorem eulerProduct_eq_Fbig (s : ℝ) (hs : 1 < s) (z : ℂ) (hz : Norm.norm z ≤ 3 / 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    (∏' p : Nat.Primes, (1 - zOmegaHom s z p)⁻¹) = Fbig s z := by
  have hmul3 : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) :=
    (tail_regroup_hasProd s hs z (by linarith) hc hmulR hposR hlogR).multipliable
  rw [split_two s hs z hz hmul3]
  rw [tail_regroup s hs z hz hc hmulR hposR hlogR]
  unfold Fbig
  have h2 : ((2 : ℂ) ^ (s : ℂ)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro hcon
    exact absurd hcon.1 (by norm_num)
  have hbridge : (1 - z * (((2 : ℕ):ℝ) ^ (-s) : ℝ))⁻¹
      = (1 - z / ((2 : ℂ) ^ (s : ℂ)))⁻¹ := by
    congr 1
    congr 1
    have hreal : (((2 : ℕ):ℝ) ^ (-s) : ℝ) = ((2 : ℝ) ^ s)⁻¹ := by
      norm_num
      rw [Real.rpow_neg (by norm_num)]
    rw [hreal]
    have hcast : (((((2 : ℝ) ^ s)⁻¹ : ℝ)) : ℂ) = ((2 : ℂ) ^ (s : ℂ))⁻¹ := by
      rw [Complex.ofReal_inv]
      congr 1
      rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hcast]
    field_simp
  rw [hbridge]
  ring

/-!
### A4 scaffold: F_k is the k-th Taylor coefficient of the Dirichlet series

Target:  (Fk k s : C) = iteratedDeriv k (fun z => sum' n, zOmegaHom s z n) 0 / k!

Route (term-by-term differentiation, k times):

Mathlib provides, in Analysis/Complex/LocallyUniformLimit.lean:
  differentiableOn_tsum_of_summable_norm  (line 171)
  hasSum_deriv_of_summable_norm           (line 182)
both taking: a summable bound u, termwise DifferentiableOn on an open U,
and ||F i w|| <= u i on U.  We use U = ball 0 (3 / 2), where A1's
zOmega_summable supplies the bound.

Sub-obligations:

C1  bound_summable j : for each j, the family
      n -> (Omega n)^j * (3 / 2)^(Omega n) * n^(-s)
    is summable.  (Polynomial factors do not break convergence because
    |z| = 3 / 2 < 2^s for s > 1; same comparison as A1 with a polynomial
    correction.)  THIS IS THE ANALYTIC INPUT.

C2  deriv_termwise j : the j-th iterated derivative of the tsum is the
    tsum of the j-th derivatives, on ball 0 (3 / 2).
    By induction on j using hasSum_deriv_of_summable_norm with C1.

C3  deriv_monomial_at_zero : iteratedDeriv k (fun z => z^m * c) 0
      = if m = k then k! * c else 0.
    Elementary; the collapse that picks out Omega n = k.

A4 follows: apply C2 at j = k, evaluate at 0 with C3, and the surviving
terms are exactly those with Omega n = k, i.e. Fk k s.
-/

/-- The norm of the z-weighted term at any n. -/
theorem zOmegaHom_norm (s : ℝ) (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    Norm.norm (zOmegaHom s z n) = Norm.norm z ^ (bigOmega n) * ((n : ℝ) ^ (-s)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  change Norm.norm (if n = 0 then 0
    else z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s : ℂ)))) = _
  rw [if_neg hn, norm_mul, norm_pow]
  congr 1
  rw [Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, Complex.ofReal_re]

/-- Polynomial growth is dominated by geometric growth, with a uniform constant. -/
theorem pow_le_const_mul_geom (j : ℕ) {c : ℝ} (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ((m : ℕ):ℝ) ^ j ≤ C * c ^ m := by
  have hlo := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) j hc
  obtain ⟨ C0, hC0 ⟩ := hlo.isBigO.bound
  obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp hC0
  refine ⟨ max (max C0 1) (((N : ℕ):ℝ) ^ j + 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 := one_pos
    have : (1 : ℝ) ≤ max C0 1 := le_max_right _ _
    calc (0 : ℝ) < 1 := h1
      _ ≤ max C0 1 := this
      _ ≤ max (max C0 1) (((N : ℕ):ℝ) ^ j + 1) := le_max_left _ _
  · intro m
    have hcm : (0 : ℝ) < c ^ m := by positivity
    have hcm1 : (1 : ℝ) ≤ c ^ m := one_le_pow₀ (le_of_lt hc)
    rcases Nat.lt_or_ge m N with hlt | hge
    · have hmN : ((m : ℕ):ℝ) ^ j ≤ ((N : ℕ):ℝ) ^ j := by
        have hmn : ((m : ℕ):ℝ) ≤ ((N : ℕ):ℝ) := by exact_mod_cast le_of_lt hlt
        gcongr
      calc ((m : ℕ):ℝ) ^ j ≤ ((N : ℕ):ℝ) ^ j := hmN
        _ ≤ (((N : ℕ):ℝ) ^ j + 1) * 1 := by linarith
        _ ≤ (((N : ℕ):ℝ) ^ j + 1) * c ^ m := by
            apply mul_le_mul_of_nonneg_left hcm1 (by positivity)
        _ ≤ max (max C0 1) (((N : ℕ):ℝ) ^ j + 1) * c ^ m := by
            apply mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hcm)
    · have hb := hN m hge
      simp only [Real.norm_eq_abs] at hb
      have habs : ((m : ℕ):ℝ) ^ j ≤ C0 * c ^ m := by
        calc ((m : ℕ):ℝ) ^ j ≤ |((m : ℕ):ℝ) ^ j| := le_abs_self _
          _ ≤ C0 * |c ^ m| := hb
          _ = C0 * c ^ m := by rw [abs_of_pos hcm]
      calc ((m : ℕ):ℝ) ^ j ≤ C0 * c ^ m := habs
        _ ≤ max (max C0 1) (((N : ℕ):ℝ) ^ j + 1) * c ^ m := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hcm)
            exact le_trans (le_max_left C0 1) (le_max_left _ _)

/-- C1 (radius form): the polynomially-weighted family at r0 is summable
when r0 < r and r satisfies the summability conditions. -/
theorem omega_pow_summable_radius (s : ℝ) (hs : 1 < s) (j : ℕ)
    (r0 r : ℝ) (hr00 : 0 < r0) (hr0r : r0 < r)
    (hr0 : 0 ≤ r) (hr3 : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) (hr2 : r < (2 : ℝ) ^ s) :
    Summable (fun n : ℕ =>
      ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n) * ((n : ℝ) ^ (-s))) := by
  have hratio : 1 < r / r0 := (one_lt_div hr00).mpr hr0r
  obtain ⟨ C, hCpos, hC ⟩ := pow_le_const_mul_geom j hratio
  have hbig : Summable (fun n : ℕ => Norm.norm (zOmegaHom s ((r : ℝ) : ℂ) n)) := by
    apply zOmega_summable_radius s hs r hr0 hr3 hr2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hscaled : Summable (fun n : ℕ => C * Norm.norm (zOmegaHom s ((r : ℝ) : ℂ) n)) :=
    hbig.mul_left C
  apply Summable.of_nonneg_of_le _ _ hscaled
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · subst hn
      norm_num
      rw [Real.zero_rpow (ne_of_lt (by linarith : (-s) < 0))]
      simp
    · have hnorm : Norm.norm (zOmegaHom s ((r : ℝ) : ℂ) n)
          = r ^ (bigOmega n) * ((n : ℝ) ^ (-s)) := by
        rw [zOmegaHom_norm s _ hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      rw [hnorm]
      have hkey : ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n)
          ≤ C * r ^ (bigOmega n) := by
        have h1 := hC (bigOmega n)
        have hr0pow : (0 : ℝ) < r0 ^ (bigOmega n) := by positivity
        calc ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n)
            ≤ (C * (r / r0) ^ (bigOmega n)) * r0 ^ (bigOmega n) := by
              apply mul_le_mul_of_nonneg_right h1 (le_of_lt hr0pow)
          _ = C * r ^ (bigOmega n) := by
              rw [div_pow]
              field_simp
      have hnn : (0 : ℝ) ≤ ((n : ℝ) ^ (-s)) := by positivity
      calc ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n) * ((n : ℝ) ^ (-s))
          ≤ (C * r ^ (bigOmega n)) * ((n : ℝ) ^ (-s)) := by
            apply mul_le_mul_of_nonneg_right hkey hnn
        _ = C * (r ^ (bigOmega n) * ((n : ℝ) ^ (-s))) := by ring


/-- C3: the k-th derivative of a monomial at 0. -/
theorem iteratedDeriv_monomial_zero (m k : ℕ) (c : ℂ) :
    iteratedDeriv k (fun z : ℂ => z ^ m * c) 0
      = if m = k then (Nat.factorial k : ℂ) * c else 0 := by
  have hbase : iteratedDeriv k (fun z : ℂ => z ^ m) 0
      = if m = k then (Nat.factorial k : ℂ) else 0 := by
    rw [iteratedDeriv_pow]
    by_cases h : m = k
    · subst h
      simp [Nat.descFactorial_self]
    · rw [if_neg h]
      rcases Nat.lt_or_ge m k with hlt | hge
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
        simp
      · have hne : m - k ≠ 0 := by omega
        rw [zero_pow hne]
        ring
  have hsplit : (fun z : ℂ => z ^ m * c) = fun z : ℂ => (z ^ m) * c := rfl
  rw [hsplit, iteratedDeriv_mul_const_field, hbase]
  by_cases h : m = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The j-th derivative of a single term. -/
theorem iteratedDeriv_zOmega_term (s : ℝ) (n : ℕ) (hn : n ≠ 0) (j : ℕ) (w : ℂ) :
    iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w
      = ((Nat.descFactorial (bigOmega n) j : ℕ) : ℂ) * w ^ (bigOmega n - j)
        * (((n : ℂ)) ^ (-(s : ℂ))) := by
  have hterm : (fun z : ℂ => zOmegaHom s z n)
      = fun z : ℂ => z ^ (bigOmega n) * (((n : ℂ)) ^ (-(s : ℂ))) := by
    funext z
    change (if n = 0 then 0 else z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s : ℂ)))) = _
    rw [if_neg hn]
  rw [hterm, iteratedDeriv_mul_const_field, iteratedDeriv_pow]

/-- Uniform bound on the j-th derivative of a term, over the ball of radius r0. -/
theorem iteratedDeriv_term_bound (s : ℝ) (hs : 1 < s) (r0 : ℝ) (hr00 : 0 < r0)
    (j : ℕ) (n : ℕ) (hn : n ≠ 0) (w : ℂ) (hw : Norm.norm w ≤ r0) :
    Norm.norm (iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w)
      ≤ ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n - j) * ((n : ℝ) ^ (-s)) := by
  rw [iteratedDeriv_zOmega_term s n hn j w]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnorm_n : Norm.norm (((n : ℂ)) ^ (-(s : ℂ))) = ((n : ℝ) ^ (-s)) := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, Complex.ofReal_re]
  rw [norm_mul, norm_mul, norm_pow, hnorm_n, Complex.norm_natCast]
  have hdesc : ((Nat.descFactorial (bigOmega n) j : ℕ) : ℝ) ≤ ((bigOmega n : ℕ) : ℝ) ^ j := by
    have h := Nat.descFactorial_le_pow (bigOmega n) j
    exact_mod_cast h
  have hwpow : Norm.norm w ^ (bigOmega n - j) ≤ r0 ^ (bigOmega n - j) := by
    gcongr
  have hnn : (0 : ℝ) ≤ ((n : ℝ) ^ (-s)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hnn
  apply mul_le_mul hdesc hwpow (by positivity) (by positivity)

/-- Summability of the derivative bound family. -/
theorem deriv_bound_summable (s : ℝ) (hs : 1 < s) (j : ℕ)
    (r0 r : ℝ) (hr01 : 1 ≤ r0) (hr0r : r0 < r)
    (hr0 : 0 ≤ r) (hr3 : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) (hr2 : r < (2 : ℝ) ^ s) :
    Summable (fun n : ℕ =>
      ((bigOmega n : ℕ) : ℝ) ^ j * r0 ^ (bigOmega n - j) * ((n : ℝ) ^ (-s))) := by
  have hbase := omega_pow_summable_radius s hs j r0 r (by linarith) hr0r hr0 hr3 hr2
  apply Summable.of_nonneg_of_le _ _ hbase
  · intro n
    positivity
  · intro n
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    gcongr
    exact Nat.sub_le _ _

/-- Each iterated derivative of a term is differentiable everywhere. -/
theorem iteratedDeriv_term_differentiable (s : ℝ) (n : ℕ) (hn : n ≠ 0) (j : ℕ) :
    Differentiable ℂ (fun w : ℂ => iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w) := by
  have heq : (fun w : ℂ => iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w)
      = fun w : ℂ => ((Nat.descFactorial (bigOmega n) j : ℕ) : ℂ) * w ^ (bigOmega n - j)
        * (((n : ℂ)) ^ (-(s : ℂ))) := by
    funext w
    exact iteratedDeriv_zOmega_term s n hn j w
  rw [heq]
  apply Differentiable.mul_const
  apply Differentiable.const_mul
  exact differentiable_pow _

/-- All iterated derivatives of the n = 0 term vanish. -/
theorem iteratedDeriv_term_zero (s : ℝ) (j : ℕ) (w : ℂ) :
    iteratedDeriv j (fun z : ℂ => zOmegaHom s z 0) w = 0 := by
  have hz : (fun z : ℂ => zOmegaHom s z 0) = fun _ : ℂ => (0 : ℂ) := by
    funext z
    exact map_zero _
  rw [hz]
  have hgen : ∀ J : ℕ, (fun v : ℂ => iteratedDeriv J (fun _ : ℂ => (0 : ℂ)) v)
      = fun _ : ℂ => (0 : ℂ) := by
    intro J
    induction J with
    | zero =>
      funext v
      simp
    | succ K IH =>
      funext v
      rw [iteratedDeriv_succ]
      have hfun : (iteratedDeriv K fun _ : ℂ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := IH
      rw [hfun, deriv_const]
  have := hgen j
  exact congrFun this w

/-- C2: term-by-term differentiation, j times, on the ball of radius 3 / 2. -/
theorem iteratedDeriv_tsum_eq (s : ℝ) (hs : 1 < s) (r0 r : ℝ)
    (hr01 : 1 ≤ r0) (hr0r : r0 < r) (hr0 : 0 ≤ r)
    (hr3 : r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2) (hr2 : r < (2 : ℝ) ^ s) :
    ∀ j : ℕ, ∀ w : ℂ, Norm.norm w < r0 →
      iteratedDeriv j (fun z : ℂ => ∑' n : ℕ, zOmegaHom s z n) w
        = ∑' n : ℕ, iteratedDeriv j (fun z : ℂ => zOmegaHom s z n) w := by
  intro j
  induction j with
  | zero =>
    intro w hw
    simp only [iteratedDeriv_zero]
  | succ J IH =>
    intro w hw
    have hball : IsOpen (Metric.ball (0 : ℂ) r0) := Metric.isOpen_ball
    have hwmem : w ∈ Metric.ball (0 : ℂ) r0 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hw
    have hbound := deriv_bound_summable s hs J r0 r hr01 hr0r hr0 hr3 hr2
    have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
        (fun v : ℂ => iteratedDeriv J (fun z : ℂ => zOmegaHom s z n) v)
        (Metric.ball (0 : ℂ) r0) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        have hzero : (fun v : ℂ => iteratedDeriv J (fun z : ℂ => zOmegaHom s z 0) v)
            = fun _ : ℂ => (0 : ℂ) := by
          funext v
          exact iteratedDeriv_term_zero s J v
        rw [hzero]
        exact differentiableOn_const 0
      · exact (iteratedDeriv_term_differentiable s n hn J).differentiableOn
    have hle : ∀ (n : ℕ) (v : ℂ), v ∈ Metric.ball (0 : ℂ) r0 →
        Norm.norm (iteratedDeriv J (fun z : ℂ => zOmegaHom s z n) v)
          ≤ ((bigOmega n : ℕ) : ℝ) ^ J * r0 ^ (bigOmega n - J) * ((n : ℝ) ^ (-s)) := by
      intro n v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      by_cases hn : n = 0
      · subst hn
        rw [iteratedDeriv_term_zero s J v, norm_zero]
        positivity
      · exact iteratedDeriv_term_bound s hs r0 (by linarith : (0 : ℝ) < r0) J n hn v (le_of_lt hv)
    have hmain := Complex.hasSum_deriv_of_summable_norm hbound hdiff hball hle hwmem
    have hIHball : (fun v : ℂ => iteratedDeriv J (fun z : ℂ => ∑' n : ℕ, zOmegaHom s z n) v)
        =ᶠ[nhds w] fun v : ℂ => ∑' n : ℕ, iteratedDeriv J (fun z : ℂ => zOmegaHom s z n) v := by
      filter_upwards [hball.mem_nhds hwmem] with v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      exact IH v hv
    rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hIHball, ← hmain.tsum_eq]
    apply tsum_congr
    intro n
    rw [iteratedDeriv_succ]

/-- The k-th derivative at 0 of a single term, in collapsed form. -/
theorem iteratedDeriv_term_at_zero (s : ℝ) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    iteratedDeriv k (fun z : ℂ => zOmegaHom s z n) 0
      = if bigOmega n = k then (Nat.factorial k : ℂ) * (((n : ℂ)) ^ (-(s : ℂ))) else 0 := by
  by_cases hn : n = 0
  · subst hn
    rw [iteratedDeriv_term_zero s k 0]
    have hO : bigOmega 0 ≠ k := by
      have : bigOmega 0 = 0 := by unfold bigOmega; simp
      omega
    rw [if_neg hO]
  · have hterm : (fun z : ℂ => zOmegaHom s z n)
        = fun z : ℂ => z ^ (bigOmega n) * (((n : ℂ)) ^ (-(s : ℂ))) := by
      funext z
      change (if n = 0 then 0 else z ^ (bigOmega n) * (((n : ℕ) : ℂ) ^ (-(s : ℂ)))) = _
      rw [if_neg hn]
    rw [hterm, iteratedDeriv_monomial_zero]

/-- Terms with Omega(n) = k >= 1 automatically have n >= 2. -/
theorem two_le_of_bigOmega_eq (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (h : bigOmega n = k) : 2 ≤ n := by
  by_contra hcon
  push Not at hcon
  interval_cases n
  · have : bigOmega 0 = 0 := by unfold bigOmega; simp
    omega
  · have : bigOmega 1 = 0 := by unfold bigOmega; simp
    omega

/-- For s > 1 there is a radius strictly between 3 / 2 and the summability threshold. -/
theorem exists_radius_gap (s : ℝ) (hs : 1 < s) :
    ∃ r : ℝ, 3 / 2 < r ∧ r * ((3 : ℝ) ^ (-s)) ≤ 1 / 2 ∧ r < (2 : ℝ) ^ s := by
  have h3s : (3 : ℝ) < (3 : ℝ) ^ s := by
    have h1 : (3 : ℝ) ^ (1 : ℝ) < (3 : ℝ) ^ s := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rwa [Real.rpow_one] at h1
  have h2s : (2 : ℝ) ≤ (2 : ℝ) ^ s := by
    have h1 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ s := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    rwa [Real.rpow_one] at h1
  set M : ℝ := min ((3 : ℝ) ^ s / 2) ((2 : ℝ) ^ s) with hM
  have hMgt : 3 / 2 < M := by
    rw [hM, lt_min_iff]
    constructor
    · linarith
    · linarith
  refine ⟨ (3 / 2 + M) / 2, by linarith, ?_, ?_⟩
  · have hle : (3 / 2 + M) / 2 ≤ (3 : ℝ) ^ s / 2 := by
      have : M ≤ (3 : ℝ) ^ s / 2 := min_le_left _ _
      linarith
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
    have hinv : (3 : ℝ) ^ (-s) = ((3 : ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    have h3spos : (0 : ℝ) < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    rw [hinv]
    have hkey : (3 / 2 + M) / 2 * ((3 : ℝ) ^ s)⁻¹ ≤ ((3 : ℝ) ^ s / 2) * ((3 : ℝ) ^ s)⁻¹ :=
      mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.mpr h3spos))
    have hsimp : ((3 : ℝ) ^ s / 2) * ((3 : ℝ) ^ s)⁻¹ = 1 / 2 := by
      field_simp
    linarith [hkey]
  · have : M ≤ (2 : ℝ) ^ s := min_le_right _ _
    linarith

/-- The Fk family is summable (real form). -/
theorem Fk_summable_subtype (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : {n : ℕ // 2 ≤ n ∧ bigOmega n = k} => ((n : ℕ):ℝ) ^ (-s)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-s))) := by
    rw [Real.summable_nat_rpow]
    linarith
  exact hbase.subtype _

/-- A4: F_k is the k-th coefficient of the Dirichlet series. -/
theorem Fk_eq_coeff_tsum (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) :
    ((Fk k s : ℝ) : ℂ)
      = iteratedDeriv k (fun z => ∑' n : ℕ, zOmegaHom s z n) 0 / (Nat.factorial k : ℂ) := by
  obtain ⟨ r, hrgt, hr3, hr2 ⟩ := exists_radius_gap s hs
  have hC2 := iteratedDeriv_tsum_eq s hs (3 / 2) r (by norm_num) hrgt
    (by linarith) hr3 hr2 k 0 (by norm_num)
  rw [hC2]
  have hcollapse : (∑' n : ℕ, iteratedDeriv k (fun z : ℂ => zOmegaHom s z n) 0)
      = ∑' n : ℕ,
        (if bigOmega n = k then (Nat.factorial k : ℂ) * (((n : ℂ)) ^ (-(s : ℂ))) else 0) := by
    apply tsum_congr
    intro n
    exact iteratedDeriv_term_at_zero s k hk n
  rw [hcollapse]
  have hfac : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpull : (∑' n : ℕ,
      (if bigOmega n = k then (Nat.factorial k : ℂ) * (((n : ℂ)) ^ (-(s : ℂ))) else 0))
      = (Nat.factorial k : ℂ) * ∑' n : ℕ,
        (if bigOmega n = k then (((n : ℂ)) ^ (-(s : ℂ))) else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases h : bigOmega n = k
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hpull]
  field_simp
  unfold Fk
  rw [Complex.ofReal_tsum]
  change (∑' x : ({n : ℕ | 2 ≤ n ∧ bigOmega n = k} : Set ℕ),
      ((((x : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) = _
  rw [tsum_subtype {n : ℕ | 2 ≤ n ∧ bigOmega n = k}
    (fun n : ℕ => (((n : ℝ) ^ (-s) : ℝ) : ℂ))]
  apply tsum_congr
  intro n
  by_cases h : bigOmega n = k
  · have hmem : n ∈ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} := by
      refine ⟨ two_le_of_bigOmega_eq k hk h, h ⟩
    rw [Set.indicator_of_mem hmem, if_pos h]
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  · have hnmem : n ∉ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} := by
      intro hcon
      exact h hcon.2
    rw [Set.indicator_of_notMem hnmem, if_neg h]

/-- OBLIGATION L2a: F_k(s) is the k-th Taylor coefficient of Fbig.
This is the number-theoretic step (Dirichlet series = Euler product). -/
theorem Fk_eq_coeff_Fbig (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    ((Fk k s : ℝ) : ℂ)
      = (iteratedDeriv k (fun z => Fbig s z) 0) / (Nat.factorial k : ℂ) := by
  have hA4 := Fk_eq_coeff_tsum k hk s hs
  rw [hA4]
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hball : Metric.ball (0 : ℂ) (3 / 2) ∈ nhds (0 : ℂ) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, dist_self]
    norm_num
  filter_upwards [hball] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzle : Norm.norm z ≤ 3 / 2 := le_of_lt hz
  have hsum := zOmega_summable s hs z hzle
  have hA2 := zOmega_eulerProduct s hs z hsum
  have hA3 := eulerProduct_eq_Fbig s hs z hzle hc hmulR hposR hlogR
  rw [← hA2, hA3]

/-- The (s-1)^(-z) factor is ContDiff of all orders. -/
theorem contDiffAt_factorA (s : ℝ) (hc : 0 < cFac s) (k : ℕ) (z : ℂ) :
    ContDiffAt ℂ k (fun w : ℂ => ((cFac s : ℝ) : ℂ) ^ w) z := by
  have hsne : ((cFac s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hc
  have hrewrite : (fun w : ℂ => ((cFac s : ℝ) : ℂ) ^ w)
      = fun w : ℂ => Complex.exp (((Real.log (cFac s) : ℝ) : ℂ) * w) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hsne]
    congr 1
    rw [← Complex.ofReal_log (le_of_lt hc)]
    try ring
  rw [hrewrite]
  apply ContDiff.contDiffAt
  exact Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)

/-- The geometric factor is ContDiff at points where the denominator is nonzero. -/
theorem contDiffAt_factorB (s : ℝ) (k : ℕ) (z : ℂ)
    (hz : 1 - z / ((2 : ℂ) ^ (s : ℂ)) ≠ 0) :
    ContDiffAt ℂ k (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) z := by
  have hden : ContDiffAt ℂ (k : ℕ) (fun w : ℂ => 1 - w / ((2 : ℂ) ^ (s : ℂ))) z := by
    apply ContDiffAt.sub contDiffAt_const
    exact ContDiffAt.div_const contDiffAt_id _
  exact hden.inv hz

/-- G2C is ContDiff at 0 (from holomorphy on ball 0 2). -/
theorem contDiffAt_factorC (s : ℝ) (hs : 1 ≤ s) (k : ℕ) :
    ContDiffAt ℂ k (fun w : ℂ => G2C s w) 0 := by
  have hball : Metric.ball (0 : ℂ) 2 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  have han : AnalyticAt ℂ (fun w : ℂ => G2C s w) 0 :=
    (G2C_differentiableOn s hs).analyticAt hball
  exact han.contDiffAt

/-- A positive real base to a complex power is ContDiff of all orders. -/
theorem contDiffAt_ofReal_cpow (a : ℝ) (ha : 0 < a) (k : ℕ) (z : ℂ) :
    ContDiffAt ℂ k (fun w : ℂ => ((a : ℝ) : ℂ) ^ w) z := by
  have hrewrite : (fun w : ℂ => ((a : ℝ) : ℂ) ^ w)
      = fun w : ℂ => Complex.exp (w * ((Real.log a : ℝ) : ℂ)) := by
    funext w
    exact ofReal_cpow_eq_exp a ha w
  rw [hrewrite]
  apply ContDiff.contDiffAt
  apply ContDiff.cexp
  exact contDiff_id.mul contDiff_const

/-- Factor A in the manuscript normalisation: (s-1)^(-z) is ContDiff of all orders. -/
theorem contDiffAt_factorAmanu (s : ℝ) (hs1 : 0 < s - 1) (k : ℕ) (z : ℂ) :
    ContDiffAt ℂ k (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) z := by
  have hrewrite : (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w))
      = fun w : ℂ => Complex.exp ((-w) * ((Real.log (s - 1) : ℝ) : ℂ)) := by
    funext w
    exact ofReal_cpow_eq_exp (s - 1) hs1 (-w)
  rw [hrewrite]
  apply ContDiff.contDiffAt
  apply ContDiff.cexp
  exact (contDiff_id.neg).mul contDiff_const

/-- Factor C in the manuscript decomposition: G2manu is ContDiff of all orders. -/
theorem contDiffAt_factorCmanu (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (k : ℕ) :
    ContDiffAt ℂ k (fun w : ℂ => G2manu s w) 0 := by
  have heq : (fun w : ℂ => G2manu s w)
      = (fun w : ℂ => ((kappaFac s : ℝ) : ℂ) ^ w) * (fun w : ℂ => G2C s w) := by
    funext w
    unfold G2manu
    simp only [Pi.mul_apply]
  rw [heq]
  exact (contDiffAt_ofReal_cpow (kappaFac s) hk k 0).mul (contDiffAt_factorC s hs k)

/-- Fbig factors as (A * B) * C in the MANUSCRIPT normalisation:
A = (s-1)^(-z), B = (1 - z / 2^s)^(-1), C = G2manu.  Parallel to Fbig_eq_prod,
which uses the cFac normalisation; both expand the same Fbig. -/
theorem Fbig_eq_prod_manu (s : ℝ) (hs : 1 < s) :
    (fun z : ℂ => Fbig s z)
      = ((fun z : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-z))
          * (fun z : ℂ => (1 - z / ((2 : ℂ) ^ (s : ℂ)))⁻¹))
        * (fun z : ℂ => G2manu s z) := by
  funext z
  rw [Fbig_eq_manuscript s hs z]
  simp only [Pi.mul_apply]

/-- Fbig factors as (A * B) * C as functions. -/
theorem Fbig_eq_prod (s : ℝ) :
    (fun z : ℂ => Fbig s z)
      = ((fun z : ℂ => ((cFac s : ℝ) : ℂ) ^ z)
          * (fun z : ℂ => (1 - z / ((2 : ℂ) ^ (s : ℂ)))⁻¹))
        * (fun z : ℂ => G2C s z) := by
  funext z
  unfold Fbig
  simp only [Pi.mul_apply]

/-- Leibniz applied twice to Fbig: the k-th iterated derivative at 0 as a
double sum with binomial coefficients. -/
theorem iteratedDeriv_Fbig (k : ℕ) (s : ℝ) (hs : 1 < s) (hc : 0 < cFac s) :
    iteratedDeriv k (fun z => Fbig s z) 0
      = ∑ n ∈ Finset.range (k + 1),
          (Nat.choose k n : ℂ) *
            (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℂ)
                * iteratedDeriv i (fun w : ℂ => ((cFac s : ℝ) : ℂ) ^ w) 0
                * iteratedDeriv (n - i) (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0)
            * iteratedDeriv (k - n) (fun w : ℂ => G2C s w) 0 := by
  have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
  have hzne : 1 - (0 : ℂ) / ((2 : ℂ) ^ (s : ℂ)) ≠ 0 := by
    simp
  have hA : ∀ j : ℕ, ContDiffAt ℂ j
      (fun w : ℂ => ((cFac s : ℝ) : ℂ) ^ w) 0 :=
    fun j => contDiffAt_factorA s hc j 0
  have hB : ∀ j : ℕ, ContDiffAt ℂ j
      (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0 :=
    fun j => contDiffAt_factorB s j 0 hzne
  have hC : ∀ j : ℕ, ContDiffAt ℂ j (fun w : ℂ => G2C s w) 0 :=
    fun j => contDiffAt_factorC s hs1 j
  have hAB : ∀ j : ℕ, ContDiffAt ℂ j
      ((fun w : ℂ => ((cFac s : ℝ) : ℂ) ^ w)
        * (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹)) 0 :=
    fun j => (hA j).mul (hB j)
  rw [Fbig_eq_prod s]
  rw [iteratedDeriv_mul (hAB k) (hC k)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_mul (hA n) (hB n)]
  try rw [Finset.sum_mul]
  try rw [Finset.mul_sum]
  try rw [Finset.sum_mul]
  try apply Finset.sum_congr rfl
  try intro i _
  try ring

/-- Double Leibniz for Fbig in the MANUSCRIPT normalisation.
Parallel to iteratedDeriv_Fbig; factor A is (s-1)^(-z) and factor C is G2manu,
so the coefficients that emerge are (-log(s-1))^l / l! as in Lemma 2.2. -/
theorem iteratedDeriv_Fbig_manu (k : ℕ) (s : ℝ) (hs : 1 < s) :
    iteratedDeriv k (fun z => Fbig s z) 0
      = ∑ n ∈ Finset.range (k + 1),
          (Nat.choose k n : ℂ) *
            (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℂ)
                * iteratedDeriv i (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) 0
                * iteratedDeriv (n - i) (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0)
            * iteratedDeriv (k - n) (fun w : ℂ => G2manu s w) 0 := by
  have hc : 0 < cFac s := cFac_pos s hs
  have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  have hk : (0 : ℝ) < kappaFac s := kappaFac_pos s hs hc
  have hzne : 1 - (0 : ℂ) / ((2 : ℂ) ^ (s : ℂ)) ≠ 0 := by
    simp
  have hA : ∀ j : ℕ, ContDiffAt ℂ j
      (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) 0 :=
    fun j => contDiffAt_factorAmanu s hsm1 j 0
  have hB : ∀ j : ℕ, ContDiffAt ℂ j
      (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0 :=
    fun j => contDiffAt_factorB s j 0 hzne
  have hC : ∀ j : ℕ, ContDiffAt ℂ j (fun w : ℂ => G2manu s w) 0 :=
    fun j => contDiffAt_factorCmanu s hs1 hk j
  have hAB : ∀ j : ℕ, ContDiffAt ℂ j
      ((fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w))
        * (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹)) 0 :=
    fun j => (hA j).mul (hB j)
  rw [Fbig_eq_prod_manu s hs]
  rw [iteratedDeriv_mul (hAB k) (hC k)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_mul (hA n) (hB n)]
  try rw [Finset.sum_mul]
  try rw [Finset.mul_sum]
  try rw [Finset.sum_mul]
  try apply Finset.sum_congr rfl
  try intro i _
  try ring

/-- The trinomial identity: C(k,n) * C(n,i) / k! = 1/(i! (n-i)! (k-n)!)
for i <= n <= k.  Verified numerically before encoding. -/
theorem choose_mul_choose_div_factorial (k n i : ℕ) (hnk : n ≤ k) (hin : i ≤ n) :
    (Nat.choose k n : ℂ) * (Nat.choose n i : ℂ)
      = (Nat.factorial k : ℂ)
        / ((Nat.factorial i : ℂ) * (Nat.factorial (n - i) : ℂ)
          * (Nat.factorial (k - n) : ℂ)) := by
  have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hfni : ((Nat.factorial (n - i) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  have hfkn : ((Nat.factorial (k - n) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - n))
  have hk : Nat.choose k n * (Nat.factorial n * Nat.factorial (k - n)) = Nat.factorial k := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hnk
  have hn : Nat.choose n i * (Nat.factorial i * Nat.factorial (n - i)) = Nat.factorial n := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hin
  rw [eq_div_iff (by exact mul_ne_zero (mul_ne_zero hfi hfni) hfkn)]
  have hkC : ((Nat.choose k n : ℕ) : ℂ)
      * (((Nat.factorial n : ℕ) : ℂ) * ((Nat.factorial (k - n) : ℕ) : ℂ))
      = ((Nat.factorial k : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hk
  have hnC : ((Nat.choose n i : ℕ) : ℂ)
      * (((Nat.factorial i : ℕ) : ℂ) * ((Nat.factorial (n - i) : ℕ) : ℂ))
      = ((Nat.factorial n : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hn
  calc (Nat.choose k n : ℂ) * (Nat.choose n i : ℂ)
        * ((Nat.factorial i : ℂ) * (Nat.factorial (n - i) : ℂ)
          * (Nat.factorial (k - n) : ℂ))
      = (Nat.choose k n : ℂ) * (Nat.factorial (k - n) : ℂ)
        * ((Nat.choose n i : ℂ)
          * ((Nat.factorial i : ℂ) * (Nat.factorial (n - i) : ℂ))) := by ring
    _ = (Nat.choose k n : ℂ) * (Nat.factorial (k - n) : ℂ)
        * (Nat.factorial n : ℂ) := by rw [hnC]
    _ = (Nat.factorial k : ℂ) := by
        rw [← hkC]
        ring

/-- The Leibniz double sum, flattened to a sum over the sigma set. -/
theorem leibniz_flatten (k : ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ n ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (n + 1), f n i
      = ∑ x ∈ (Finset.range (k + 1)).sigma (fun n => Finset.range (n + 1)),
          f x.1 x.2 := by
  rw [Finset.sum_sigma]

/-- The convolution double sum, flattened to a sum over its sigma set. -/
theorem conv_flatten (k : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k - p + 1), g p q
      = ∑ x ∈ (Finset.range (k + 1)).sigma (fun p => Finset.range (k - p + 1)),
          g x.1 x.2 := by
  rw [Finset.sum_sigma]

theorem sigma_reindex (k : ℕ) (F : ℕ → ℕ → ℂ) (G : ℕ → ℕ → ℂ)
    (hval : ∀ n i : ℕ, i ≤ n → n ≤ k → F n i = G (n - i) (k - n)) :
    ∑ x ∈ (Finset.range (k + 1)).sigma (fun n => Finset.range (n + 1)), F x.1 x.2
      = ∑ y ∈ (Finset.range (k + 1)).sigma (fun p => Finset.range (k - p + 1)), G y.1 y.2 := by
  apply Finset.sum_nbij'
    (i := fun x : Sigma (fun _ : ℕ => ℕ) => Sigma.mk (x.1 - x.2) (k - x.1))
    (j := fun y : Sigma (fun _ : ℕ => ℕ) => Sigma.mk (k - y.2) (k - y.2 - y.1))
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have h2 : x.1 - (x.1 - x.2) = x.2 := by omega
    have h3 : k - (k - x.1) = x.1 := by omega
    simp only [h3, h2]
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    have h1 : k - y.2 - (k - y.2 - y.1) = y.1 := by omega
    have h2 : k - (k - y.2) = y.2 := by omega
    simp only [h1, h2]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    exact hval x.1 x.2 (by omega) (by omega)

theorem L2b_summand (k : ℕ) (s : ℝ) (hs : 1 < s) (n i : ℕ) (hin : i ≤ n) (hnk : n ≤ k) :
    (Nat.choose k n : ℂ) *
        ((Nat.choose n i : ℂ)
          * ((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
          * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
        * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s)
      / (Nat.factorial k : ℂ)
      = gCoeff (k - n) s * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)
        * ((((Real.log (cFac s)) ^ (k - (n - i) - (k - n))
            / (Nat.factorial (k - (n - i) - (k - n))) : ℝ)) : ℂ) := by
  have hidx : k - (n - i) - (k - n) = i := by omega
  rw [hidx]
  have hkfac : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have htri := choose_mul_choose_div_factorial k n i hnk hin
  rw [div_eq_iff hkfac]
  have hassoc : (Nat.choose k n : ℂ) *
      ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
        * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
      * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s)
      = ((Nat.choose k n : ℂ) * (Nat.choose n i : ℂ)) *
        (((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
          * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ))
          * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s)) := by ring
  rw [hassoc, htri]
  have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hfni : ((Nat.factorial (n - i) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  have hfkn : ((Nat.factorial (k - n) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - n))
  field_simp
  try ring

/-- OBLIGATION L2b: the k-th coefficient of Fbig is the triple convolution
of the three factors' coefficients. -/
theorem coeff_Fbig_eq_convolution (k : ℕ) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2)
    (hc : 0 < cFac s) :
    (iteratedDeriv k (fun z => Fbig s z) 0) / (Nat.factorial k : ℂ)
      = ∑ p ∈ Finset.range (k + 1),
          ∑ q ∈ Finset.range (k - p + 1),
            gCoeff q s * (((2 : ℝ) ^ (-(p : ℝ) * s) : ℝ) : ℂ)
              * ((((Real.log (cFac s)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ) := by
  have hAval : ∀ i : ℕ,
      iteratedDeriv i (fun w : ℂ => ((cFac s : ℝ) : ℂ) ^ w) 0
        = (Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ) := by
    intro i
    have h := coeff_cpow s hc i
    have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    field_simp at h
    linear_combination h
  have hBval : ∀ j : ℕ,
      iteratedDeriv j (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0
        = (Nat.factorial j : ℂ) * ((((2 : ℝ) ^ (-(j : ℝ) * s) : ℝ)) : ℂ) := by
    intro j
    have h := coeff_geom s hs j
    have hfj : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    rw [div_eq_iff hfj] at h
    rw [h]
    ring
  have hCval : ∀ q : ℕ,
      iteratedDeriv q (fun w : ℂ => G2C s w) 0 = (Nat.factorial q : ℂ) * gCoeff q s := by
    intro q
    unfold gCoeff
    have hfq : ((Nat.factorial q : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
    field_simp
  rw [iteratedDeriv_Fbig k s hs hc]
  simp only [hAval, hBval, hCval]
  rw [Finset.sum_div]
  have hdist : ∀ n ∈ Finset.range (k + 1),
      ((Nat.choose k n : ℂ) *
        (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
            * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))) *
        ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s) / (Nat.factorial k : ℂ)
      = ∑ i ∈ Finset.range (n + 1), (Nat.choose k n : ℂ) *
          ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
            * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
          * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s) / (Nat.factorial k : ℂ) := by
    intro n _
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_congr rfl hdist]
  rw [leibniz_flatten k (fun n i => (Nat.choose k n : ℂ) *
    ((Nat.choose n i : ℂ)
      * ((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
      * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
    * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s) / (Nat.factorial k : ℂ))]
  rw [conv_flatten k (fun p q => gCoeff q s * (((2 : ℝ) ^ (-(p : ℝ) * s) : ℝ) : ℂ)
    * ((((Real.log (cFac s)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ))]
  exact sigma_reindex k
    (fun n i => (Nat.choose k n : ℂ) *
      ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((Real.log (cFac s)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
        * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
      * ((Nat.factorial (k - n) : ℂ) * gCoeff (k - n) s) / (Nat.factorial k : ℂ))
    (fun p q => gCoeff q s * (((2 : ℝ) ^ (-(p : ℝ) * s) : ℝ) : ℂ)
      * ((((Real.log (cFac s)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ))
    (fun n i hin hnk => L2b_summand k s hs n i hin hnk)

/-- Manuscript g_i(s) = [z^i] G2(s,z), in the manuscript normalisation. -/
noncomputable def gManu (i : ℕ) (s : ℝ) : ℂ :=
  (iteratedDeriv i (fun z => G2manu s z) 0) / (i.factorial : ℂ)

theorem L2b_summand_manu (k : ℕ) (s : ℝ) (hs : 1 < s) (n i : ℕ) (hin : i ≤ n) (hnk : n ≤ k) :
    (Nat.choose k n : ℂ) *
        ((Nat.choose n i : ℂ)
          * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
          * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
        * ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s)
      / (Nat.factorial k : ℂ)
      = gManu (k - n) s * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)
        * ((((-Real.log (s - 1)) ^ (k - (n - i) - (k - n))
            / (Nat.factorial (k - (n - i) - (k - n))) : ℝ)) : ℂ) := by
  have hidx : k - (n - i) - (k - n) = i := by omega
  rw [hidx]
  have hkfac : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have htri := choose_mul_choose_div_factorial k n i hnk hin
  rw [div_eq_iff hkfac]
  have hassoc : (Nat.choose k n : ℂ) *
      ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
        * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
      * ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s)
      = ((Nat.choose k n : ℂ) * (Nat.choose n i : ℂ)) *
        (((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
          * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ))
          * ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s)) := by ring
  rw [hassoc, htri]
  have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hfni : ((Nat.factorial (n - i) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  have hfkn : ((Nat.factorial (k - n) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - n))
  field_simp
  try ring

/-- Coefficient convolution for Fbig in the MANUSCRIPT normalisation:
[z^k] Fbig = sum over p,q of g_q(s) 2^(-ps) (-log(s-1))^(k-p-q)/(k-p-q)!. -/
theorem coeff_Fbig_eq_convolution_manu (k : ℕ) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
    (iteratedDeriv k (fun z => Fbig s z) 0) / (Nat.factorial k : ℂ)
      = ∑ p ∈ Finset.range (k + 1),
          ∑ q ∈ Finset.range (k - p + 1),
            gManu q s * (((2 : ℝ) ^ (-(p : ℝ) * s) : ℝ) : ℂ)
              * ((((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ) := by
  have hAval : ∀ i : ℕ,
      iteratedDeriv i (fun w : ℂ => ((s - 1 : ℝ) : ℂ) ^ (-w)) 0
        = (Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ) := by
    intro i
    have h := coeff_pow_neg s hs i
    have hfi : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    field_simp at h
    linear_combination h
  have hBval : ∀ j : ℕ,
      iteratedDeriv j (fun w : ℂ => (1 - w / ((2 : ℂ) ^ (s : ℂ)))⁻¹) 0
        = (Nat.factorial j : ℂ) * ((((2 : ℝ) ^ (-(j : ℝ) * s) : ℝ)) : ℂ) := by
    intro j
    have h := coeff_geom s hs j
    have hfj : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    rw [div_eq_iff hfj] at h
    rw [h]
    ring
  have hCval : ∀ q : ℕ,
      iteratedDeriv q (fun w : ℂ => G2manu s w) 0 = (Nat.factorial q : ℂ) * gManu q s := by
    intro q
    unfold gManu
    have hfq : ((Nat.factorial q : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
    field_simp
  rw [iteratedDeriv_Fbig_manu k s hs]
  simp only [hAval, hBval, hCval]
  rw [Finset.sum_div]
  have hdist : ∀ n ∈ Finset.range (k + 1),
      ((Nat.choose k n : ℂ) *
        (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
            * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))) *
        ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s) / (Nat.factorial k : ℂ)
      = ∑ i ∈ Finset.range (n + 1), (Nat.choose k n : ℂ) *
          ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
            * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
          * ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s) / (Nat.factorial k : ℂ) := by
    intro n _
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_congr rfl hdist]
  rw [leibniz_flatten k (fun n i => (Nat.choose k n : ℂ) *
    ((Nat.choose n i : ℂ)
      * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
      * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
    * ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s) / (Nat.factorial k : ℂ))]
  rw [conv_flatten k (fun p q => gManu q s * (((2 : ℝ) ^ (-(p : ℝ) * s) : ℝ) : ℂ)
    * ((((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ))]
  exact sigma_reindex k
    (fun n i => (Nat.choose k n : ℂ) *
      ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) * ((((-Real.log (s - 1)) ^ i / (Nat.factorial i) : ℝ)) : ℂ))
        * ((Nat.factorial (n - i) : ℂ) * ((((2 : ℝ) ^ (-((n - i : ℕ):ℝ) * s) : ℝ)) : ℂ)))
      * ((Nat.factorial (k - n) : ℂ) * gManu (k - n) s) / (Nat.factorial k : ℂ))
    (fun p q => gManu q s * (((2 : ℝ) ^ (-(p : ℝ) * s) : ℝ) : ℂ)
      * ((((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q)) : ℝ)) : ℂ))
    (fun n i hin hnk => L2b_summand_manu k s hs n i hin hnk)

/-- MANUSCRIPT LEMMA 2.2 (manuscript normalisation):
F_k(s) = sum_{i+j+l=k} g_i(s) 2^(-js) (-log(s-1))^l / l!.
This is the form Definition 2.3 and Lemma 2.4 consume. -/
theorem Fk_expansion_manu (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
    Fk k s = ∑ p ∈ Finset.range (k + 1),
      ∑ q ∈ Finset.range (k - p + 1),
        (gManu q s).re * (2 : ℝ) ^ (-((p : ℝ)) * s)
          * ((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q))) := by
  have hc : 0 < cFac s := cFac_pos s hs
  have hmulR := cFac_multipliable s hs
  have hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹ := by
    intro p
    obtain ⟨h3, hp⟩ := cFac_factor_le_third s hs p
    exact inv_pos.mpr (by linarith)
  have hlogR := cFac_log_summable s hs
  have hC := (Fk_eq_coeff_Fbig k hk s hs hs2 hc hmulR hposR hlogR).trans (coeff_Fbig_eq_convolution_manu k s hs hs2)
  have hre : ((Fk k s : ℝ) : ℂ).re = Fk k s := Complex.ofReal_re _
  rw [← hre, hC]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- MANUSCRIPT LEMMA 2.2: the exact expansion of F_k(s). -/
theorem Fk_expansion (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2)
    (hc : 0 < cFac s)
    (hmulR : Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))
    (hposR : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p}, 0 < (1 - ((p : ℕ):ℝ) ^ (-s))⁻¹)
    (hlogR : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((1 - ((p : ℕ):ℝ) ^ (-s))⁻¹))) :
    Fk k s = ∑ p ∈ Finset.range (k + 1),
      ∑ q ∈ Finset.range (k - p + 1),
        (gCoeff q s).re * (2 : ℝ) ^ (-((p : ℝ)) * s)
          * ((Real.log (cFac s)) ^ (k - p - q) / (Nat.factorial (k - p - q))) := by
  have hC := (Fk_eq_coeff_Fbig k hk s hs hs2 hc hmulR hposR hlogR).trans (coeff_Fbig_eq_convolution k s hs hs2 hc)
  have hre : ((Fk k s : ℝ) : ℂ).re = Fk k s := Complex.ofReal_re _
  rw [← hre, hC]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

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
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hind : Summable (Set.indicator {n : ℕ | 2 ≤ n ∧ bigOmega n = k}
      (fun n : ℕ => 1 / ((n : ℝ) * Real.log n))) := by
    set I := Set.indicator {n : ℕ | 2 ≤ n ∧ bigOmega n = k}
      (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) with hI
    have hInn : ∀ n : ℕ, 0 ≤ I n := by
      intro n
      rw [hI]
      apply Set.indicator_nonneg
      intro a ha
      obtain ⟨ha2, _⟩ := ha
      have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
      have hla : (0 : ℝ) < Real.log a := Real.log_pos (by linarith)
      exact le_of_lt (one_div_pos.mpr (mul_pos (by linarith) hla))
    have hIvan : ∀ n : ℕ, ¬(2 ≤ n ∧ bigOmega n = k) → I n = 0 := by
      intro n hn
      rw [hI, Set.indicator_apply,
        if_neg (show n ∉ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} from fun hmem => hn hmem)]
    have hImem : ∀ n : ℕ, 2 ≤ n → bigOmega n = k →
        I n = 1 / ((n : ℝ) * Real.log n) := by
      intro n h2 hO
      rw [hI, Set.indicator_apply,
        if_pos (show n ∈ {n : ℕ | 2 ≤ n ∧ bigOmega n = k} from ⟨h2, hO⟩)]
    have hblock : ∀ N j : ℕ, 1 ≤ j →
        ∑ n ∈ (Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j), I n
          ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
            (1 / ((j : ℝ) * Real.sqrt j)) := by
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
          I n ≤ 1 / ((2 : ℝ) ^ j * Real.log ((2 : ℝ) ^ j)) := by
        intro n hn
        obtain ⟨hnf, hn2, hnO⟩ := Finset.mem_filter.mp hn
        have hb := dyadic_fiber_mem_bounds 1 N j n hnf
        have h2j : (((2 : ℕ) ^ j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hb.1
        have h2jR : (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
        rw [h2jR] at h2j
        have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
          calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
            _ ≤ (2 : ℝ) ^ j := by
                apply pow_le_pow_right₀ (by norm_num) hj
        rw [hImem n hn2 hnO]
        exact inv_mul_log_le ((2 : ℝ) ^ j) (n : ℝ) h2le h2j
      have hsum1 := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at hsum1
      have hbpos : (0 : ℝ) < 1 / ((2 : ℝ) ^ j * Real.log ((2 : ℝ) ^ j)) := by
        apply one_div_pos.mpr
        apply mul_pos (by positivity)
        rw [Real.log_pow]
        exact mul_pos (by exact_mod_cast (by omega : 0 < j)) hl2
      have hcast2 : (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
        push_cast
        ring
      have hcard := block_count_le_piK k j N
      rw [hcast2] at hcard
      have hcardR : (((((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
            (fun n => 2 ≤ n ∧ bigOmega n = k)).card : ℕ) : ℝ)
          ≤ (piK k ((2 : ℝ) ^ (j + 1)) : ℝ) := by
        exact_mod_cast hcard
      have h4n : (4 : ℕ) ≤ 2 ^ (j + 1) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hx3 : (3 : ℝ) ≤ (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) := by
        have h4r : (4 : ℝ) ≤ (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h4n
        linarith
      have hpk := hbound (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) hx3
      rw [hcast2] at hpk
      calc ∑ n ∈ ((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
            (fun n => 2 ≤ n ∧ bigOmega n = k), I n
          ≤ (((((Finset.Ioc 1 N).filter (fun n => Nat.log 2 n = j)).filter
              (fun n => 2 ≤ n ∧ bigOmega n = k)).card : ℕ) : ℝ) *
              (1 / ((2 : ℝ) ^ j * Real.log ((2 : ℝ) ^ j))) := hsum1
        _ ≤ (piK k ((2 : ℝ) ^ (j + 1)) : ℝ) *
              (1 / ((2 : ℝ) ^ j * Real.log ((2 : ℝ) ^ j))) :=
            mul_le_mul_of_nonneg_right hcardR hbpos.le
        _ ≤ C * (2 : ℝ) ^ (j + 1) * (Real.log (Real.log ((2 : ℝ) ^ (j + 1)))) ^ (k - 1) /
              Real.log ((2 : ℝ) ^ (j + 1)) * (1 / ((2 : ℝ) ^ j * Real.log ((2 : ℝ) ^ j))) :=
            mul_le_mul_of_nonneg_right hpk hbpos.le
        _ ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
              (1 / ((j : ℝ) * Real.sqrt j)) :=
            block_arith C hC (k - 1) j hj
    have hKnn : (0 : ℝ) ≤ 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 :=
      div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * C)
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
          1 / ((j : ℝ) * Real.sqrt j) ≤ 3 := by
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
          have h11 : (1 : ℝ) / (((1 : ℕ):ℝ) * Real.sqrt ((1 : ℕ):ℝ)) = 1 := by
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
                (1 / ((j : ℝ) * Real.sqrt j)) :=
              Finset.sum_le_sum (fun j hjm => hblock N j (Finset.mem_Icc.mp hjm).1)
          _ = 4 * C * (2 * ((k - 1 : ℕ):ℝ)) ^ (k - 1) / (Real.log 2) ^ 2 *
              ∑ j ∈ Finset.Icc 1 (Nat.log 2 N), (1 / ((j : ℝ) * Real.sqrt j)) := by
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
    (f := fun n : ℕ => 1 / ((n : ℝ) * Real.log n))).mpr hind

/-- MANUSCRIPT PROPOSITION 2.5 (exact decomposition).
E(k) = -q(2k U_k - V_k) - Delta(k) - E_1(k) + E_exp(k), q = log 2 / 4.
Every term is deterministic; no estimates enter.  Verified symbolically
before encoding. -/
theorem prop_2_5 (k : ℕ) (hk : 1 ≤ k) :
    Ek k = -(Real.log 2 / 4) * (2 * (k : ℝ) * Uk k - Vk k)
             - DeltaConv k - E1k k + Eexpk k := by
  have hlem21 : f k = Ik k + Tk k := lemma1_foundation k hk (fk_summable k hk)
  have hexp := Ikfrozen_re_expand k
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hIk : Ik k = Dk k + (Ikfrozen k).re := by
    unfold Dk
    ring
  unfold Ek E1k Eexpk aOneConst
  rw [hlem21, hIk, hexp]
  unfold Dk
  field_simp
  ring


/-- MANUSCRIPT section 7: the aggregate source bound, DERIVED.

|2E(k) - E(k+1)| <= RBound, from Proposition 2.5 (the exact decomposition),
Theorem 4.1 via deltaConv_le, and section 3.5 via the E_1 bound.  The U/V term
and E_exp stay as certified hypotheses, as in the manuscript.

This is what makes sections 2, 4 and 3.5 reach the final theorem: previously
NumericalFacts asserted this bound outright, leaving Prop 2.5 and Theorem 4.1
proved but unused. -/
theorem source_bound_derived (k : ℕ) (hk : 1 ≤ k)
    (Sstar alph Umax Vmax : ℝ)
    (hS : ∀ m : ℕ,
      ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * |(cCoeff i).re| ≤ Sstar)
    (hE1 : ∀ m : ℕ, 1 ≤ m → |E1k m| ≤ alph * ((m : ℝ) + 1))
    (hUV : |2 * (2 * (k : ℝ) * Uk k - Vk k)
             - (2 * ((k : ℝ) + 1) * Uk (k + 1) - Vk (k + 1))|
           ≤ (2 * (k : ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax)
    (hEexp : ∀ m : ℕ, |Eexpk m| ≤ 1.45 / (k : ℝ) + 1e-3) :
    |2 * Ek k - Ek (k + 1)| ≤ RBound Umax Vmax Sstar alph k := by
  have hk1 : 1 ≤ k + 1 := by omega
  rw [prop_2_5 k hk, prop_2_5 (k + 1) hk1]
  have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hD := deltaConv_le k Sstar deltaM_abs_le (hS k)
  have hD1 := deltaConv_le (k + 1) Sstar deltaM_abs_le (hS (k + 1))
  have hA := hE1 k hk
  have hA1 := hE1 (k + 1) hk1
  rw [hcast] at hA1
  have hX := hEexp k
  have hX1 := hEexp (k + 1)
  have hq : (0:ℝ) < Real.log 2 / 4 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  unfold RBound
  have habs := abs_le.mp hUV
  have hDa := abs_le.mp hD
  have hD1a := abs_le.mp hD1
  have hAa := abs_le.mp hA
  have hA1a := abs_le.mp hA1
  have hXa := abs_le.mp hX
  have hX1a := abs_le.mp hX1
  rw [abs_le]
  constructor <;> nlinarith [habs.1, habs.2, hDa.1, hDa.2, hD1a.1, hD1a.2,
    hAa.1, hAa.2, hA1a.1, hA1a.2, hXa.1, hXa.2, hX1a.1, hX1a.2, hq]

/-- The p = 2 half of Lemma 3.9's c: d/ds log(1 - 2^(-s)) = log 2 / (2^s - 1). -/
theorem deriv_log_one_sub_two_pow (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t : ℝ => Real.log (1 - (2 : ℝ) ^ (-t)))
      (Real.log 2 / ((2 : ℝ) ^ s - 1)) s := by
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hlt : (2 : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h1 : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h1
    linarith
  have hpos : (0 : ℝ) < 1 - (2 : ℝ) ^ (-s) := by linarith
  have hinner : HasDerivAt (fun t : ℝ => 1 - (2 : ℝ) ^ (-t))
      ((2 : ℝ) ^ (-s) * Real.log 2) s := by
    have hbase : HasDerivAt (fun t : ℝ => (2 : ℝ) ^ (-t))
        (-((2 : ℝ) ^ (-s) * Real.log 2)) s := by
      have hrw : (fun t : ℝ => (2 : ℝ) ^ (-t))
          = fun t : ℝ => Real.exp ((-t) * Real.log 2) := by
        funext t
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      rw [hrw]
      have hinner : HasDerivAt (fun t : ℝ => (-t) * Real.log 2) (-Real.log 2) s := by
        simpa using (hasDerivAt_neg s).mul_const (Real.log 2)
      have h := hinner.exp
      convert h using 1
      rw [show Real.exp (-s * Real.log 2) = (2 : ℝ) ^ (-s) by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf]
      ring
    simpa using hbase.const_sub 1
  have h := (Real.hasDerivAt_log (ne_of_gt hpos)).comp s hinner
  simp only [Function.comp_def] at h
  have hval : Real.log 2 / ((2 : ℝ) ^ s - 1)
      = (1 - (2 : ℝ) ^ (-s))⁻¹ * ((2 : ℝ) ^ (-s) * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : ((2 : ℝ) ^ s) ≠ 0 := ne_of_gt h2s
    field_simp
  rw [hval]
  exact h

/-- d/ds [log 2 / (2^s - 1)] = -log^2(2) 2^s / (2^s - 1)^2.
The second derivative of the p = 2 part of Lemma 3.9's c.
Verified numerically at s = 1.3, 1.7, 2.0. -/
theorem deriv_two_pow_term (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t : ℝ => Real.log 2 / ((2 : ℝ) ^ t - 1))
      (-((Real.log 2) ^ 2 * (2 : ℝ) ^ s) / ((2 : ℝ) ^ s - 1) ^ 2) s := by
  have h2s : (2 : ℝ) ≤ (2 : ℝ) ^ s := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hs)
  have hne : (2 : ℝ) ^ s - 1 ≠ 0 := by intro hcon; linarith
  have hbase : HasDerivAt (fun t : ℝ => (2 : ℝ) ^ t) ((2 : ℝ) ^ s * Real.log 2) s := by
    have hrw : (fun t : ℝ => (2 : ℝ) ^ t)
        = fun t : ℝ => Real.exp (t * Real.log 2) := by
      funext t
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
    rw [hrw]
    have hinner : HasDerivAt (fun t : ℝ => t * Real.log 2) (Real.log 2) s := by
      simpa using (hasDerivAt_id s).mul_const (Real.log 2)
    have h := hinner.exp
    convert h using 1
    rw [show Real.exp (s * Real.log 2) = (2 : ℝ) ^ s by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]]
  have hden : HasDerivAt (fun t : ℝ => (2 : ℝ) ^ t - 1) ((2 : ℝ) ^ s * Real.log 2) s := by
    simpa using hbase.sub_const 1
  have hstep := (hasDerivAt_const s (Real.log 2)).div hden hne
  have hval : -((Real.log 2) ^ 2 * (2 : ℝ) ^ s) / ((2 : ℝ) ^ s - 1) ^ 2
      = (0 * ((2 : ℝ) ^ s - 1) - Real.log 2 * ((2 : ℝ) ^ s * Real.log 2))
        / ((2 : ℝ) ^ s - 1) ^ 2 := by
    field_simp
    ring
  rw [hval]
  exact hstep

/-- d/ds of the kappa-part of c, given f' as a hypothesis.
f' is assumed for the same reason f is: the manuscript certifies
f = (log zeta(s)(s-1))' numerically from Stieltjes constants, so its
derivative is certified the same way rather than derived. -/
theorem hasDerivAt_kappa_part (z : ℂ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1 : ℝ) 2)
    (f fp : ℝ → ℝ)
    (hfp : HasDerivAt f (fp s) s) :
    HasDerivAt (fun t : ℝ =>
        z * (((f t + Real.log 2 / ((2 : ℝ) ^ t - 1) : ℝ)) : ℂ))
      (z * (((fp s + -((Real.log 2) ^ 2 * (2 : ℝ) ^ s) / ((2 : ℝ) ^ s - 1) ^ 2 : ℝ)) : ℂ)) s := by
  have hs1 : 1 < s := hsmem.1
  have hsum := hfp.add (deriv_two_pow_term s hs1)
  have hcast := hsum.ofReal_comp
  exact hcast.const_mul z

/-- G2manu is differentiable in z on the closed disc of radius 12 / 5, for each
fixed s.  The s-independent half of Lemma 3.8; generalises
G2at1_differentiableOn_wide from s = 1. -/
theorem G2manu_differentiableOn_wide (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) :
    DifferentiableOn ℂ (fun z : ℂ => G2manu s z) (Metric.closedBall (0 : ℂ) (12 / 5 : ℝ)) := by
  have hsub : Metric.closedBall (0 : ℂ) (12 / 5 : ℝ) ⊆ Metric.ball (0 : ℂ) (29 / 10) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcpow : DifferentiableOn ℂ (fun z : ℂ => ((kappaFac s : ℝ) : ℂ) ^ z)
      (Metric.closedBall (0 : ℂ) (12 / 5 : ℝ)) := by
    apply Differentiable.differentiableOn
    intro z
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hk
  have hG2C : DifferentiableOn ℂ (fun z : ℂ => G2C s z)
      (Metric.closedBall (0 : ℂ) (12 / 5 : ℝ)) :=
    (G2C_differentiableOn_wide s hs).mono hsub
  unfold G2manu
  exact hcpow.mul hG2C

/-- Lemma 3.8's contour representation: g_i(s) is the i-th Cauchy coefficient
of G2(s, .) on |z| = 12 / 5.  Since cauchyPowerSeries is defined by the contour
integral, this is the manuscript's
  g_i(s) = (1 / 2 pi i) * contour_{|z|=R} G2(s,z) z^(-i-1) dz,
and it is what makes differentiating in s under the contour available. -/
theorem gManu_eq_cauchy_coeff (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (i : ℕ) :
    gManu i s = (cauchyPowerSeries (fun z : ℂ => G2manu s z) 0 (12 / 5 : NNReal)).coeff i := by
  have hR : (0 : NNReal) < 12 / 5 := by norm_num
  have hser := (G2manu_differentiableOn_wide s hs hk).hasFPowerSeriesOnBall hR
  have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser i
  unfold gManu
  rw [hbridge]
  have hfac : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  field_simp

/-- log p <= sqrt p for p >= 3.  Lets the differentiated log-series be
compared against a plain p-series rather than needing sum log p / p^2. -/
theorem log_le_sqrt (x : ℝ) (hx : 3 ≤ x) : Real.log x ≤ x ^ ((1 : ℝ)/2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : (0 : ℝ) < x ^ ((1 : ℝ)/2) := Real.rpow_pos_of_pos hx0 _
  have hq : (0 : ℝ) < x ^ ((1 : ℝ)/4) := Real.rpow_pos_of_pos hx0 _
  have hkey : Real.log x = 4 * Real.log (x ^ ((1 : ℝ)/4)) := by
    rw [Real.log_rpow hx0]
    ring
  have hy := Real.log_le_sub_one_of_pos hq
  have hsplit : x ^ ((1 : ℝ)/2) = (x ^ ((1 : ℝ)/4)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (x ^ ((1 : ℝ)/4)) 2, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  rw [hkey, hsplit]
  nlinarith [hy, sq_nonneg (x ^ ((1 : ℝ)/4) - 2)]

/-- log^2 p <= (64 / 9) p^(3 / 4) for p >= 3.
From log y <= y - 1 at y = p^(3 / 8): log p = (8 / 3) log y <= (8 / 3)(y-1) <= (8 / 3)y,
so log^2 p <= (64 / 9) y^2 = (64 / 9) p^(3 / 4).
Needed for the r=2 chain, where the per-term derivative carries log^2 p and
log_le_sqrt (exponent 1 / 2) is too tight -- log^2 p > sqrt p already at p = 5. -/
theorem log_sq_le (x : ℝ) (hx : 3 ≤ x) :
    (Real.log x) ^ 2 ≤ (64 / 9) * x ^ ((3 : ℝ)/4) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy : (0 : ℝ) < x ^ ((3 : ℝ)/8) := Real.rpow_pos_of_pos hx0 _
  have hlogy : Real.log (x ^ ((3 : ℝ)/8)) ≤ x ^ ((3 : ℝ)/8) - 1 :=
    Real.log_le_sub_one_of_pos hy
  have hlogx : Real.log x = (8 / 3) * Real.log (x ^ ((3 : ℝ)/8)) := by
    rw [Real.log_rpow hx0]
    ring
  have hbound : Real.log x ≤ (8 / 3) * x ^ ((3 : ℝ)/8) := by
    rw [hlogx]
    nlinarith [hlogy, hy]
  have hnn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : x ^ ((3 : ℝ)/4) = (x ^ ((3 : ℝ)/8)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (x ^ ((3 : ℝ)/8)) 2, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  rw [hsq]
  nlinarith [hbound, hnn, hy]

/-- The log^2-weighted series is dominated by a p-series, uniformly for s >= 1:
log^2 p * p^(-2s) <= (64 / 9) p^(3 / 4 - 2s) <= (64 / 9) p^(-5 / 4).
The r=2 analogue of deriv_series_summable. -/
theorem deriv2_series_summable (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (Real.log ((p : ℕ):ℝ)) ^ 2 * (((p : ℕ):ℝ)) ^ (-2*s)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (64 / 9) * (((p : ℕ):ℝ)) ^ (-(5 : ℝ)/4)) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 : ℝ)/4)) := by
      rw [Real.summable_nat_rpow]
      norm_num
    exact (hbase.subtype _).mul_left (64 / 9)
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro p
    have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    positivity
  · intro p
    have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
    have hlog := log_sq_le (((p : ℕ):ℝ)) hp3
    have hpos : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (-2*s) := Real.rpow_pos_of_pos hp0 _
    have hstep : (Real.log ((p : ℕ):ℝ)) ^ 2 * (((p : ℕ):ℝ)) ^ (-2*s)
        ≤ ((64 / 9) * (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4)) * (((p : ℕ):ℝ)) ^ (-2*s) :=
      mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    have hcomb : ((64 / 9) * (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4)) * (((p : ℕ):ℝ)) ^ (-2*s)
        = (64 / 9) * (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4 + -2*s) := by
      rw [mul_assoc, ← Real.rpow_add hp0]
    have hmono : (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4 + -2*s) ≤ (((p : ℕ):ℝ)) ^ (-(5 : ℝ)/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [hcomb] at hstep
    nlinarith [hstep, hmono, hpos]

/-- The differentiated log-series is dominated by a p-series, uniformly for
s >= 1: log p * p^(-2s) <= p^(1 / 2 - 2s) <= p^(-3 / 2).
This is the estimate behind both Lemma 3.8's "product converging locally
uniformly" and Lemma 3.9's termwise differentiation. -/
theorem deriv_series_summable (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-2*s)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (((p : ℕ):ℝ)) ^ (-(3 : ℝ)/2)) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ)/2)) := by
      rw [Real.summable_nat_rpow]
      norm_num
    exact hbase.subtype _
  apply Summable.of_nonneg_of_le _ _ hcomp
  · intro p
    have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
    have hlog : (0 : ℝ) ≤ Real.log ((p : ℕ):ℝ) := Real.log_nonneg (by linarith)
    positivity
  · intro p
    have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < ((p : ℕ):ℝ) := by linarith
    have hlog := log_le_sqrt ((p : ℕ):ℝ) hp3
    have hstep : Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-2*s)
        ≤ (((p : ℕ):ℝ)) ^ ((1 : ℝ)/2) * (((p : ℕ):ℝ)) ^ (-2*s) := by
      apply mul_le_mul_of_nonneg_right hlog (by positivity)
    have hcomb : (((p : ℕ):ℝ)) ^ ((1 : ℝ)/2) * (((p : ℕ):ℝ)) ^ (-2*s)
        = (((p : ℕ):ℝ)) ^ ((1 : ℝ)/2 - 2*s) := by
      rw [← Real.rpow_add hp0]
      ring_nf
    have hmono : (((p : ℕ):ℝ)) ^ ((1 : ℝ)/2 - 2*s) ≤ (((p : ℕ):ℝ)) ^ (-(3 : ℝ)/2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [hcomb] at hstep
    linarith

/-- The single derivative computation behind Lemma 3.9's per-prime term:
d/ds log(1 - c*p^(-s)) = c*log p*p^(-s)/(1 - c*p^(-s)).
Applied at c = z and c = 1 to get the two halves of the log-factor.
Verified numerically at (p,s,c) = (3,1.4,1.3),(5,1.7,0.9),(11,1.2,1),(3,1,2). -/
theorem deriv_log_one_sub_const_rpow (p : ℕ) (hp : 3 ≤ p) (c s : ℝ)
    (hne : (1 : ℝ) - c * ((p : ℝ)) ^ (-s) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (1 - c * ((p : ℝ)) ^ (-t)))
      (c * Real.log (p : ℝ) * ((p : ℝ)) ^ (-s) / (1 - c * ((p : ℝ)) ^ (-s))) s := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hbase : HasDerivAt (fun t : ℝ => ((p : ℝ)) ^ (-t))
      (-(((p : ℝ)) ^ (-s) * Real.log (p : ℝ))) s := by
    have hrw : (fun t : ℝ => ((p : ℝ)) ^ (-t))
        = fun t : ℝ => Real.exp ((-t) * Real.log (p : ℝ)) := by
      funext t
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    rw [hrw]
    have hinner : HasDerivAt (fun t : ℝ => (-t) * Real.log (p : ℝ))
        (-Real.log (p : ℝ)) s := by
      simpa using (hasDerivAt_neg s).mul_const (Real.log (p : ℝ))
    have h := hinner.exp
    convert h using 1
    rw [show Real.exp (-s * Real.log (p : ℝ)) = ((p : ℝ)) ^ (-s) by
      rw [Real.rpow_def_of_pos hp0, mul_comm]]
    ring
  have hin : HasDerivAt (fun t : ℝ => 1 - c * ((p : ℝ)) ^ (-t))
      (c * (((p : ℝ)) ^ (-s) * Real.log (p : ℝ))) s := by
    have h := (hbase.const_mul c).const_sub 1
    have hval2 : c * (((p : ℝ)) ^ (-s) * Real.log (p : ℝ))
        = -(c * -(((p : ℝ)) ^ (-s) * Real.log (p : ℝ))) := by ring
    rw [hval2]
    exact h
  have h := (Real.hasDerivAt_log hne).comp s hin
  simp only [Function.comp_def] at h
  have hval : c * Real.log (p : ℝ) * ((p : ℝ)) ^ (-s) / (1 - c * ((p : ℝ)) ^ (-s))
      = (1 - c * ((p : ℝ)) ^ (-s))⁻¹ * (c * (((p : ℝ)) ^ (-s) * Real.log (p : ℝ))) := by
    field_simp
  rw [hval]
  exact h

/-- Lemma 3.9's per-prime term, assembled from two applications of
deriv_log_one_sub_const_rpow (at c = z and c = 1).
The cancellation between the two logs is what produces p^(-2s) decay;
bounding them separately would give only p^(-s), which is not summable. -/
theorem deriv_log_prime_factor (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -Real.log (1 - z * ((p : ℝ)) ^ (-t)) + z * Real.log (1 - ((p : ℝ)) ^ (-t)))
      (-(z * (z - 1) * Real.log (p : ℝ))
        / ((((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z))) s := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (3 : ℝ) ≤ ((p : ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p : ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hneg : ((p : ℝ)) ^ (-s) = (((p : ℝ)) ^ s)⁻¹ := Real.rpow_neg (le_of_lt hp0) s
  have hpsinv : ((p : ℝ)) ^ (-s) ≤ 1 / 3 := by
    rw [hneg, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hppos : (0 : ℝ) < ((p : ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hzabs := abs_le.mp hz
  have hne1 : (1 : ℝ) - z * ((p : ℝ)) ^ (-s) ≠ 0 := by
    have : z * ((p : ℝ)) ^ (-s) ≤ 2 / 3 := by nlinarith [hzabs.2, hppos, hpsinv]
    intro hcon
    have : z * ((p : ℝ)) ^ (-s) = 1 := by linarith
    linarith
  have hne2 : (1 : ℝ) - (1 : ℝ) * ((p : ℝ)) ^ (-s) ≠ 0 := by
    rw [one_mul]
    intro hcon
    have : ((p : ℝ)) ^ (-s) = 1 := by linarith
    linarith
  have hpz : ((p : ℝ)) ^ s - z ≠ 0 := by
    have h2 := hzabs.2
    intro hcon
    linarith
  have hp1 : ((p : ℝ)) ^ s - 1 ≠ 0 := by
    intro hcon
    linarith
  have hA : HasDerivAt (fun t : ℝ => -Real.log (1 - z * ((p : ℝ)) ^ (-t)))
      (-(z * Real.log (p : ℝ) * ((p : ℝ)) ^ (-s) / (1 - z * ((p : ℝ)) ^ (-s)))) s :=
    (deriv_log_one_sub_const_rpow p hp z s hne1).neg
  have hB : HasDerivAt (fun t : ℝ => z * Real.log (1 - ((p : ℝ)) ^ (-t)))
      (z * (Real.log (p : ℝ) * ((p : ℝ)) ^ (-s) / (1 - ((p : ℝ)) ^ (-s)))) s := by
    have h := (deriv_log_one_sub_const_rpow p hp 1 s hne2).const_mul z
    simpa using h
  have hsum := hA.add hB
  have hval : -(z * (z - 1) * Real.log (p : ℝ))
        / ((((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z))
      = -(z * Real.log (p : ℝ) * ((p : ℝ)) ^ (-s) / (1 - z * ((p : ℝ)) ^ (-s)))
        + z * (Real.log (p : ℝ) * ((p : ℝ)) ^ (-s) / (1 - ((p : ℝ)) ^ (-s))) := by
    have hps0 : ((p : ℝ)) ^ s ≠ 0 := by
      intro hcon; rw [hcon] at hps; linarith
    rw [hneg]
    rw [show (1 : ℝ) - z * (((p : ℝ)) ^ s)⁻¹ = (((p : ℝ)) ^ s - z) / ((p : ℝ)) ^ s by
      field_simp]
    rw [show (1 : ℝ) - (((p : ℝ)) ^ s)⁻¹ = (((p : ℝ)) ^ s - 1) / ((p : ℝ)) ^ s by
      field_simp]
    field_simp
    ring
  rw [hval]
  exact hsum

/-- The pointwise bound feeding hasDerivAt_tsum_of_isPreconnected:
|z(z-1) log p / ((p^s-1)(p^s-z))| <= 27 log p p^(-2s) for p >= 3, s >= 1, |z| <= 2.
Crude route: |z(z-1)| <= 6, p^s - 1 >= (2 / 3)p^s, |p^s - z| >= (1 / 3)p^s. -/
theorem deriv_prime_term_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(-(z * (z - 1) * Real.log (p : ℝ))
        / ((((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z)))|
      ≤ 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-2*s) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (3 : ℝ) ≤ ((p : ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p : ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0 : ℝ) < ((p : ℝ)) ^ s := by linarith
  have hzabs := abs_le.mp hz
  have hlogpos : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hnum : |z * (z - 1) * Real.log (p : ℝ)| ≤ 6 * Real.log (p : ℝ) := by
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg hlogpos]
    have h1 : |z| ≤ 2 := hz
    have h2 : |z - 1| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [hzabs.1, hzabs.2]
    have hprod : |z| * |z - 1| ≤ 6 := by nlinarith [abs_nonneg z, abs_nonneg (z - 1), h1, h2]
    nlinarith [hprod, hlogpos]
  have hd1 : (2 / 3) * ((p : ℝ)) ^ s ≤ ((p : ℝ)) ^ s - 1 := by linarith
  have hd2 : (1 / 3) * ((p : ℝ)) ^ s ≤ ((p : ℝ)) ^ s - z := by
    linarith [hzabs.2]
  have hden : (2 / 9) * (((p : ℝ)) ^ s) ^ 2
      ≤ (((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z) := by
    nlinarith [hd1, hd2, hps0]
  have hdenpos : (0 : ℝ) < (((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z) := by nlinarith [hps0]
  have hsq : (((p : ℝ)) ^ s) ^ 2 = ((p : ℝ)) ^ (2*s) := by
    rw [← Real.rpow_natCast (((p : ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
    norm_num
    ring_nf
  rw [abs_div, abs_neg]
  rw [div_le_iff₀ (by rwa [abs_of_pos hdenpos])]
  rw [abs_of_pos hdenpos]
  have hpow : ((p : ℝ)) ^ (-2*s) * ((p : ℝ)) ^ (2*s) = 1 := by
    rw [← Real.rpow_add hp0]
    norm_num
  have hstep : |z * (z - 1) * Real.log (p : ℝ)| ≤ 6 * Real.log (p : ℝ) := hnum
  have hrhs : 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-2*s)
        * ((((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z))
      ≥ 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-2*s) * ((2 / 9) * (((p : ℝ)) ^ s) ^ 2) := by
    have hc : (0 : ℝ) ≤ 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-2*s) := by
      have : (0 : ℝ) < ((p : ℝ)) ^ (-2*s) := Real.rpow_pos_of_pos hp0 _
      positivity
    exact mul_le_mul_of_nonneg_left hden hc
  have hsimp : 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-2*s) * ((2 / 9) * (((p : ℝ)) ^ s) ^ 2)
      = 6 * Real.log (p : ℝ) := by
    rw [hsq]
    have : ((p : ℝ)) ^ (-2*s) * ((p : ℝ)) ^ (2*s) = 1 := hpow
    nlinarith [this]
  linarith [hstep, hrhs, hsimp]

/-- s-free version of the per-prime bound.  hasDerivAt_tsum_of_isPreconnected
needs a dominating function independent of the point, so we replace p^(-2s)
by p^(-2), valid since s >= 1 and p >= 3 > 1. -/
theorem deriv_prime_term_bound_uniform (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(-(z * (z - 1) * Real.log (p : ℝ))
        / ((((p : ℝ)) ^ s - 1) * (((p : ℝ)) ^ s - z)))|
      ≤ 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-(2 : ℝ)) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogpos : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hbase := deriv_prime_term_bound p hp s hs z hz
  have hmono : ((p : ℝ)) ^ (-2*s) ≤ ((p : ℝ)) ^ (-(2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have : 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-2*s)
      ≤ 27 * Real.log (p : ℝ) * ((p : ℝ)) ^ (-(2 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left hmono
    linarith
  linarith

/-- The s-free dominator is summable. -/
theorem deriv_bound_uniform_summable :
    Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))) := by
  have h := deriv_series_summable 1 (le_refl 1)
  have heq : (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-2*(1 : ℝ)))
      = fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := by
    funext p
    norm_num
  rw [heq] at h
  have h27 := h.mul_left 27
  apply h27.congr
  intro p
  ring

theorem hasDerivAt_log_series (z : ℝ) (hz : |z| ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-Real.log (1 - z * (((p : ℕ):ℝ)) ^ (-t))
          + z * Real.log (1 - (((p : ℕ):ℝ)) ^ (-t))))
      (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-(z * (z - 1) * Real.log ((p : ℕ):ℝ))
          / (((((p : ℕ):ℝ)) ^ s - 1) * ((((p : ℕ):ℝ)) ^ s - z)))) s := by
  have hy0 : (3 / 2 : ℝ) ∈ Set.Ioo (1 : ℝ) 2 := by
    constructor <;> norm_num
  have hconv : Summable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      -Real.log (1 - z * (((p : ℕ):ℝ)) ^ (-(3 / 2:ℝ)))
        + z * Real.log (1 - (((p : ℕ):ℝ)) ^ (-(3 / 2:ℝ)))) :=
    (prime_correction_summable (3 / 2) (by norm_num) z hz).of_abs
  have hshape : (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-(z * (z - 1) * Real.log ((p : ℕ):ℝ))
          / ((((p : ℕ):ℝ)) ^ s - 1) / ((((p : ℕ):ℝ)) ^ s - z)))
      = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-(z * (z - 1) * Real.log ((p : ℕ):ℝ))
          / (((((p : ℕ):ℝ)) ^ s - 1) * ((((p : ℕ):ℝ)) ^ s - z))) := by
    apply tsum_congr
    intro p
    rw [div_div]
  rw [← hshape]
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun (p : {p : ℕ // p.Prime ∧ 3 ≤ p}) (t : ℝ) =>
      -Real.log (1 - z * (((p : ℕ):ℝ)) ^ (-t))
        + z * Real.log (1 - (((p : ℕ):ℝ)) ^ (-t)))
    (g' := fun (p : {p : ℕ // p.Prime ∧ 3 ≤ p}) (t : ℝ) =>
      -(z * (z - 1) * Real.log ((p : ℕ):ℝ))
        / ((((p : ℕ):ℝ)) ^ t - 1) / ((((p : ℕ):ℝ)) ^ t - z))
    deriv_bound_uniform_summable isOpen_Ioo isPreconnected_Ioo _ _ hy0 hconv hsmem
  · intro p y hy
    rw [div_div]
    exact deriv_log_prime_factor (p : ℕ) p.2.2 y (le_of_lt hy.1) z hz
  · intro p y hy
    rw [Real.norm_eq_abs, div_div]
    exact deriv_prime_term_bound_uniform (p : ℕ) p.2.2 y (le_of_lt hy.1) z hz

/-- kappa(s) = zetaTilde(s) * (1 - 2^(-s)) for s > 1.
Real-part projection of cFac_eq_zeta.  This is what lets Lemma 3.9's kappa-part
split into f(s) + log 2/(2^s - 1), with f = (log zetaTilde)' carried opaquely
(the manuscript certifies f numerically via Stieltjes constants). -/
theorem kappaFac_eq_zetaTilde (s : ℝ) (hs : 1 < s) :
    kappaFac s = zetaTilde s * (1 - (2 : ℝ) ^ (-s)) := by
  have hne : s ≠ 1 := ne_of_gt hs
  have hcast : ((1 : ℂ) - ((2 : ℂ)) ^ (-(s : ℂ))) = (((1 - (2 : ℝ) ^ (-s) : ℝ)) : ℂ) := by
    push_cast
    rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) by norm_num]
    rw [show (-(s : ℂ)) = (((-s : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
  have hz := cFac_eq_zeta s hs
  rw [hcast] at hz
  have hre : cFac s = (riemannZeta (s : ℂ)).re * (1 - (2 : ℝ) ^ (-s)) := by
    have := congrArg Complex.re hz
    simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using this
  unfold kappaFac zetaTilde
  rw [if_neg hne, hre]
  ring

/-- Each regularised factor is positive for real z with |z| <= 2, p >= 3, s >= 1. -/
theorem reg_factor_real_pos (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    0 < (1 - z * ((p : ℝ)) ^ (-s))⁻¹ * (1 - ((p : ℝ)) ^ (-s)) ^ z := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hppos : (0 : ℝ) < ((p : ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hthird : ((p : ℝ)) ^ (-s) ≤ 1 / 3 := by
    have h1 : ((p : ℝ)) ^ (-s) ≤ ((p : ℝ)) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : ((p : ℝ))⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hzabs := abs_le.mp hz
  have hden : (0 : ℝ) < 1 - z * ((p : ℝ)) ^ (-s) := by
    nlinarith [hzabs.2, hppos, hthird]
  have hbase : (0 : ℝ) < 1 - ((p : ℝ)) ^ (-s) := by linarith
  have h1 : (0 : ℝ) < (1 - z * ((p : ℝ)) ^ (-s))⁻¹ := inv_pos.mpr hden
  have h2 : (0 : ℝ) < (1 - ((p : ℝ)) ^ (-s)) ^ z := Real.rpow_pos_of_pos hbase z
  exact mul_pos h1 h2

/-- The real regularised family is multipliable: its logs are summable
(prime_correction_summable) and each factor is positive. -/
theorem reg_multipliable_three_real (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} =>
      (1 - z * (((p : ℕ):ℝ)) ^ (-s))⁻¹ * (1 - (((p : ℕ):ℝ)) ^ (-s)) ^ z) := by
  apply Real.multipliable_of_summable_log
  · intro p
    exact reg_factor_real_pos (p : ℕ) p.2.2 s hs z hz
  · have hsum := (prime_correction_summable s hs z hz).of_abs
    apply hsum.congr
    intro p
    have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
    have hpos := reg_factor_real_pos (p : ℕ) p.2.2 s hs z hz
    have hppos : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
    have hzabs := abs_le.mp hz
    have hthird : (((p : ℕ):ℝ)) ^ (-s) ≤ 1 / 3 := by
      have h1 : (((p : ℕ):ℝ)) ^ (-s) ≤ (((p : ℕ):ℝ)) ^ (-(1 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      rw [Real.rpow_neg_one] at h1
      have h2 : ((((p : ℕ):ℝ)))⁻¹ ≤ 1 / 3 := by
        rw [inv_le_comm₀ hp0 (by norm_num)]
        linarith
      linarith
    have hden : (0 : ℝ) < 1 - z * (((p : ℕ):ℝ)) ^ (-s) := by
      nlinarith [hzabs.2, hppos, hthird]
    have hbase : (0 : ℝ) < 1 - (((p : ℕ):ℝ)) ^ (-s) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_rpow hbase]

/-- The log of the real regularised p >= 3 product is the sum of the logs.
This is what turns hasDerivAt_log_series (a statement about the tsum) into a
statement about the product, i.e. about log G2 restricted to its p >= 3 part. -/
theorem log_reg_tprod_real (s : ℝ) (hs : 1 ≤ s) (z : ℝ) (hz : |z| ≤ 2) :
    Real.log (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * (((p : ℕ):ℝ)) ^ (-s))⁻¹ * (1 - (((p : ℕ):ℝ)) ^ (-s)) ^ z)
      = ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-Real.log (1 - z * (((p : ℕ):ℝ)) ^ (-s))
          + z * Real.log (1 - (((p : ℕ):ℝ)) ^ (-s))) := by
  have hlogeq : ∀ p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      Real.log ((1 - z * (((p : ℕ):ℝ)) ^ (-s))⁻¹ * (1 - (((p : ℕ):ℝ)) ^ (-s)) ^ z)
        = -Real.log (1 - z * (((p : ℕ):ℝ)) ^ (-s))
          + z * Real.log (1 - (((p : ℕ):ℝ)) ^ (-s)) := by
    intro p
    have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
    have hppos : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (-s) := Real.rpow_pos_of_pos hp0 _
    have hthird : (((p : ℕ):ℝ)) ^ (-s) ≤ 1 / 3 := by
      have h1 : (((p : ℕ):ℝ)) ^ (-s) ≤ (((p : ℕ):ℝ)) ^ (-(1 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      rw [Real.rpow_neg_one] at h1
      have h2 : ((((p : ℕ):ℝ)))⁻¹ ≤ 1 / 3 := by
        rw [inv_le_comm₀ hp0 (by norm_num)]
        linarith
      linarith
    have hzabs := abs_le.mp hz
    have hden : (0 : ℝ) < 1 - z * (((p : ℕ):ℝ)) ^ (-s) := by
      nlinarith [hzabs.2, hppos, hthird]
    have hbase : (0 : ℝ) < 1 - (((p : ℕ):ℝ)) ^ (-s) := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_rpow hbase]
  rw [log_tprod_real
    (fun p : {p : ℕ // p.Prime ∧ 3 ≤ p} => reg_factor_real_pos (p : ℕ) p.2.2 s hs z hz)
    (reg_multipliable_three_real s hs z hz)
    (by
      have hsum := (prime_correction_summable s hs z hz).of_abs
      apply hsum.congr
      intro p
      exact (hlogeq p).symm)]
  exact tsum_congr hlogeq

/-- Lemma 3.9's prime part, stated on the product rather than the sum:
d/ds log(prod_{p>=3} regularised factor) = sum_p -z(z-1) log p/((p^s-1)(p^s-z)).
Combines hasDerivAt_log_series with log_reg_tprod_real, transferring the
derivative across the pointwise identity on the open interval. -/
theorem hasDerivAt_log_reg_tprod (z : ℝ) (hz : |z| ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => Real.log (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (1 - z * (((p : ℕ):ℝ)) ^ (-t))⁻¹ * (1 - (((p : ℕ):ℝ)) ^ (-t)) ^ z))
      (∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
        (-(z * (z - 1) * Real.log ((p : ℕ):ℝ))
          / (((((p : ℕ):ℝ)) ^ s - 1) * ((((p : ℕ):ℝ)) ^ s - z)))) s := by
  have hbase := hasDerivAt_log_series z hz s hsmem
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact log_reg_tprod_real t (le_of_lt ht.1) z hz

/-- zetaTilde is positive on (1,2]: kappa = zetaTilde * (1 - 2^-s) is positive
and the second factor is. -/
theorem zetaTilde_pos (s : ℝ) (hs : 1 < s) : 0 < zetaTilde s := by
  have hk := kappaFac_pos s hs (cFac_pos s hs)
  rw [kappaFac_eq_zetaTilde s hs] at hk
  have hlt : (2 : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h1 : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h1
    linarith
  have h2 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-s) := by linarith
  nlinarith [hk, h2]

/-- `log(zetaTilde)` is differentiable on (1,2).

This DISCHARGES the `hf` hypothesis that six lemmas in this file thread
through unproved -- `lemma_3_8_integral_r1`, `gManu_eq_circleIntegral`'s
companion, `lemma_3_9_complex` and the three around them all take
`HasDerivAt (fun t => Real.log (zetaTilde t)) (f x) x` as given.

`zetaTilde t = (t - 1) * (riemannZeta t).re` off `t = 1`, and since `x > 1`
that description holds on a whole neighbourhood of `x`, which is what lets the
`if` be discharged.  `riemannZeta` is complex-differentiable away from its one
pole at 1; composing with the real embedding and with `.re` gives real
differentiability, and `zetaTilde_pos` puts the value strictly inside the
domain of `Real.log`.

Stated in the `HasDerivAt f (deriv f x) x` form the consumers use, so they can
be instantiated at `f := deriv (fun t => Real.log (zetaTilde t))`. -/
theorem log_zetaTilde_hasDerivAt (x : ℝ) (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => Real.log (zetaTilde t))
      (deriv (fun t : ℝ => Real.log (zetaTilde t)) x) x := by
  have hx1 : (1 : ℝ) < x := hx.1
  have hcne : ((x : ℂ)) ≠ 1 := by
    intro hc
    have : (x : ℝ) = 1 := by exact_mod_cast hc
    linarith
  -- Re zeta through the real embedding: the `real_of_complex` idiom of
  -- `zetaRderiv_eq_re` in Odd/Basic.lean, which is the proven way to
  -- differentiate `t |-> (F t).re` here.
  have hzC : DifferentiableAt ℂ riemannZeta ((x : ℂ)) :=
    differentiableAt_riemannZeta hcne
  have hzre : HasDerivAt (fun t : ℝ => (riemannZeta ((t : ℂ))).re)
      ((deriv riemannZeta ((x : ℂ))).re) x := hzC.hasDerivAt.real_of_complex
  have hid : HasDerivAt (fun t : ℝ => t - 1) (1 : ℝ) x := by
    have h := (hasDerivAt_id x).sub_const 1
    simpa using h
  have hprod : HasDerivAt (fun t : ℝ => (t - 1) * (riemannZeta ((t : ℂ))).re)
      ((1 : ℝ) * (riemannZeta ((x : ℂ))).re
        + (x - 1) * (deriv riemannZeta ((x : ℂ))).re) x := hid.mul hzre
  -- off t = 1 the `if` takes its else branch, and that holds on a whole
  -- neighbourhood of x since x > 1
  have hev : (fun t : ℝ => zetaTilde t)
      =ᶠ[nhds x] (fun t : ℝ => (t - 1) * (riemannZeta ((t : ℂ))).re) := by
    filter_upwards [Ioi_mem_nhds hx1] with t ht
    have htne : t ≠ 1 := ne_of_gt ht
    unfold zetaTilde
    rw [if_neg htne]
  have hzt : DifferentiableAt ℝ (fun t : ℝ => zetaTilde t) x :=
    hprod.differentiableAt.congr_of_eventuallyEq hev
  have hpos : 0 < zetaTilde x := zetaTilde_pos x hx1
  have hlog : DifferentiableAt ℝ (fun t : ℝ => Real.log (zetaTilde t)) x :=
    hzt.log hpos.ne'
  exact hlog.hasDerivAt

/-- The p = 2 factor is positive on (1,2]. -/
theorem one_sub_two_pow_pos (s : ℝ) (hs : 1 < s) : (0 : ℝ) < 1 - (2 : ℝ) ^ (-s) := by
  have hlt : (2 : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    have h1 : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ s :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
    rw [Real.rpow_one] at h1
    linarith
  linarith

/-- MANUSCRIPT LEMMA 3.9, real-z case.  With G2 = kappa^z * (regularised
p >= 3 product), log G2 = z log kappa + log(product), and
  d/ds [that] = z * (log 2/(2^s-1) + f(s) - sum_p (z-1) log p/((p^s-1)(p^s-z))).
f is a hypothesis, not derived: the manuscript certifies it numerically from
FLINT Stieltjes constants rather than expanding it.

SCOPE: real z only.  Section 3.5's beta_i and section 6.1's gammahat_i extract
[z^i] coefficients and need the COMPLEX analogue -- the same chain over C,
where Complex.log's branch cuts make the per-factor step harder than a
transcription.  This real case validates the architecture; it does not
discharge 3.5 or 6.1. -/
theorem lemma_3_9_real (z : ℝ) (hz : |z| ≤ 2) (s : ℝ) (hsmem : s ∈ Set.Ioo (1 : ℝ) 2)
    (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ =>
        z * (Real.log (zetaTilde t) + Real.log (1 - (2 : ℝ) ^ (-t)))
          + Real.log (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
              (1 - z * (((p : ℕ):ℝ)) ^ (-t))⁻¹ * (1 - (((p : ℕ):ℝ)) ^ (-t)) ^ z))
      (z * (f s + Real.log 2 / ((2 : ℝ) ^ s - 1))
        + ∑' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
            (-(z * (z - 1) * Real.log ((p : ℕ):ℝ))
              / (((((p : ℕ):ℝ)) ^ s - 1) * ((((p : ℕ):ℝ)) ^ s - z)))) s := by
  have hs1 : 1 < s := hsmem.1
  have hkap := hf.add (deriv_log_one_sub_two_pow s hs1)
  have hprod := hasDerivAt_log_reg_tprod z hz s hsmem
  exact (hkap.const_mul z).add hprod

/-- The complex argument 1 - c*p^(-s) lies in the slit plane, for ||c|| <= 2,
p >= 3, s >= 1: its distance from 1 is at most 2 / 3, so its real part exceeds
1 / 3.  This is the side condition Complex.hasDerivAt_log needs. -/
theorem one_sub_mem_slitPlane (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (c : ℂ) (hc : Norm.norm c ≤ 2) :
    (1 : ℂ) - c * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ) ∈ Complex.slitPlane := by
  have hp3 : (3 : ℝ) ≤ ((p : ℕ):ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < ((p : ℕ):ℝ) := by linarith
  have hppos : (0 : ℝ) < ((p : ℕ):ℝ) ^ (-s) := Real.rpow_pos_of_pos hp0 _
  have hthird : ((p : ℕ):ℝ) ^ (-s) ≤ 1 / 3 := by
    have h1 : ((p : ℕ):ℝ) ^ (-s) ≤ ((p : ℕ):ℝ) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      linarith
    rw [Real.rpow_neg_one] at h1
    have h2 : (((p : ℕ):ℝ))⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hnorm : Norm.norm (c * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) ≤ 2 / 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos]
    nlinarith [norm_nonneg c, hc, hthird, hppos]
  rw [Complex.mem_slitPlane_iff]
  left
  have hre : (((1 : ℂ) - c * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ))).re
      = 1 - (c * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)).re := by
    simp
  rw [hre]
  have habs : |(c * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)).re|
      ≤ Norm.norm (c * ((((p : ℕ):ℝ) ^ (-s) : ℝ) : ℂ)) := Complex.abs_re_le_norm _
  have := abs_le.mp (le_trans habs hnorm)
  linarith [this.2]

/-- The real derivative of t |-> p^(-t), extracted so both the real and the
complex chains can use it. -/
theorem hasDerivAt_rpow_neg (p : ℕ) (hp : 3 ≤ p) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ((p : ℝ)) ^ (-t))
      (-(((p : ℝ)) ^ (-s) * Real.log (p : ℝ))) s := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hrw : (fun t : ℝ => ((p : ℝ)) ^ (-t))
      = fun t : ℝ => Real.exp ((-t) * Real.log (p : ℝ)) := by
    funext t
    rw [Real.rpow_def_of_pos hp0, mul_comm]
  rw [hrw]
  have hinner : HasDerivAt (fun t : ℝ => (-t) * Real.log (p : ℝ))
      (-Real.log (p : ℝ)) s := by
    simpa using (hasDerivAt_neg s).mul_const (Real.log (p : ℝ))
  have h := hinner.exp
  convert h using 1
  rw [show Real.exp (-s * Real.log (p : ℝ)) = ((p : ℝ)) ^ (-s) by
    rw [Real.rpow_def_of_pos hp0, mul_comm]]
  ring

/-- d/dt p^t = p^t log p.  Positive-exponent mirror of hasDerivAt_rpow_neg,
needed for the r=2 per-prime derivative where p^s appears in the denominators. -/
theorem hasDerivAt_rpow_pos (p : ℕ) (hp : 3 ≤ p) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ((p : ℝ)) ^ t)
      (((p : ℝ)) ^ s * Real.log (p : ℝ)) s := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hrw : (fun t : ℝ => ((p : ℝ)) ^ t)
      = fun t : ℝ => Real.exp (t * Real.log (p : ℝ)) := by
    funext t
    rw [Real.rpow_def_of_pos hp0, mul_comm]
  rw [hrw]
  have hinner : HasDerivAt (fun t : ℝ => t * Real.log (p : ℝ)) (Real.log (p : ℝ)) s := by
    simpa using (hasDerivAt_id s).mul_const (Real.log (p : ℝ))
  have h := hinner.exp
  convert h using 1
  rw [show Real.exp (s * Real.log (p : ℝ)) = ((p : ℝ)) ^ s by
    rw [Real.rpow_def_of_pos hp0, mul_comm]]

/-- The r=2 per-prime derivative:
d/ds [-(z-1) log p / ((p^s-1)(p^s-z))]
  = (z-1) log^2 p * p^s * ((p^s-z) + (p^s-1)) / ((p^s-1)^2 (p^s-z)^2).
Verified numerically at (p,s,z) = (3,1.4,1.3), (5,1.7,0.9), (11,1.2,1.8). -/
theorem deriv2_prime_term (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -((z - 1) * Real.log (p : ℝ)) / (((p : ℝ)) ^ t - 1) / (((p : ℝ)) ^ t - z))
      ((z - 1) * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ s)
        * (((((p : ℝ)) ^ s - z) + (((p : ℝ)) ^ s - 1)))
        / ((((p : ℝ)) ^ s - 1) ^ 2 * ((((p : ℝ)) ^ s - z)) ^ 2)) s := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (3 : ℝ) ≤ ((p : ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p : ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hzabs := abs_le.mp hz
  have hd1 : ((p : ℝ)) ^ s - 1 ≠ 0 := by intro hcon; linarith
  have hd2 : ((p : ℝ)) ^ s - z ≠ 0 := by
    intro hcon
    have := hzabs.2
    linarith
  have hbase := hasDerivAt_rpow_pos p hp s
  have hA : HasDerivAt (fun t : ℝ => ((p : ℝ)) ^ t - 1)
      (((p : ℝ)) ^ s * Real.log (p : ℝ)) s := by
    simpa using hbase.sub_const 1
  have hB : HasDerivAt (fun t : ℝ => ((p : ℝ)) ^ t - z)
      (((p : ℝ)) ^ s * Real.log (p : ℝ)) s := by
    simpa using hbase.sub_const z
  have hstep1 := (hasDerivAt_const s (-((z - 1) * Real.log (p : ℝ)))).div hA hd1
  have hstep2 := hstep1.div hB hd2
  have hval : (z - 1) * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ s)
        * (((((p : ℝ)) ^ s - z) + (((p : ℝ)) ^ s - 1)))
        / ((((p : ℝ)) ^ s - 1) ^ 2 * ((((p : ℝ)) ^ s - z)) ^ 2)
      = ((0 * (((p : ℝ)) ^ s - 1) - -((z - 1) * Real.log (p : ℝ))
            * (((p : ℝ)) ^ s * Real.log (p : ℝ))) / (((p : ℝ)) ^ s - 1) ^ 2
          * (((p : ℝ)) ^ s - z)
        - -((z - 1) * Real.log (p : ℝ)) / (((p : ℝ)) ^ s - 1)
            * (((p : ℝ)) ^ s * Real.log (p : ℝ)))
        / (((p : ℝ)) ^ s - z) ^ 2 := by
    field_simp
    ring
  rw [hval]
  exact hstep2

/-- Uniform bound for the r=2 per-prime derivative:
|d/ds term| <= 200 log^2 p p^(-2), s-free for s >= 1.
Crude route: |z-1| <= 3, (p^s-z)+(p^s-1) <= 2p^s, (p^s-1)^2 >= (4 / 9)p^(2s),
(p^s-z)^2 >= (1 / 9)p^(2s), giving 9/(4 / 81) = 182.25; 200 leaves margin. -/
theorem deriv2_prime_term_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℝ) (hz : |z| ≤ 2) :
    |(z - 1) * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ s)
        * (((((p : ℝ)) ^ s - z) + (((p : ℝ)) ^ s - 1)))
        / ((((p : ℝ)) ^ s - 1) ^ 2 * ((((p : ℝ)) ^ s - z)) ^ 2)|
      ≤ 200 * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ (-(2 : ℝ))) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (3 : ℝ) ≤ ((p : ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p : ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0 : ℝ) < ((p : ℝ)) ^ s := by linarith
  have hzabs := abs_le.mp hz
  have hlog0 : (0 : ℝ) ≤ (Real.log (p : ℝ)) ^ 2 := sq_nonneg _
  have hnum : |(z - 1) * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ s)
        * (((((p : ℝ)) ^ s - z) + (((p : ℝ)) ^ s - 1)))|
      ≤ 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hlog0, abs_of_pos hps0]
    have h1 : |z - 1| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hzabs.1, hzabs.2]
    have h2 : |(((p : ℝ)) ^ s - z) + (((p : ℝ)) ^ s - 1)| ≤ 3 * ((p : ℝ)) ^ s := by
      rw [abs_le]
      constructor
      · linarith [hzabs.2, hps]
      · linarith [hzabs.1, hps]
    calc |z - 1| * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ s
          * |(((p : ℝ)) ^ s - z) + (((p : ℝ)) ^ s - 1)|
        ≤ 3 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ s * (3 * ((p : ℝ)) ^ s) := by
          apply mul_le_mul _ h2 (abs_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hps0)
          exact mul_le_mul_of_nonneg_right h1 hlog0
      _ = 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by ring
  have hd1 : (2 / 3) * ((p : ℝ)) ^ s ≤ ((p : ℝ)) ^ s - 1 := by linarith
  have hd2 : (1 / 3) * ((p : ℝ)) ^ s ≤ ((p : ℝ)) ^ s - z := by linarith [hzabs.2]
  have hd1pos : (0 : ℝ) < ((p : ℝ)) ^ s - 1 := by linarith
  have hd2pos : (0 : ℝ) < ((p : ℝ)) ^ s - z := by linarith [hzabs.2]
  have hsq1 : (4 / 9) * ((((p : ℝ)) ^ s)) ^ 2 ≤ (((p : ℝ)) ^ s - 1) ^ 2 := by
    nlinarith [hd1, hps0]
  have hsq2 : (1 / 9) * ((((p : ℝ)) ^ s)) ^ 2 ≤ ((((p : ℝ)) ^ s - z)) ^ 2 := by
    nlinarith [hd2, hps0]
  have hden : (4 / 81) * ((((p : ℝ)) ^ s)) ^ 4
      ≤ (((p : ℝ)) ^ s - 1) ^ 2 * ((((p : ℝ)) ^ s - z)) ^ 2 := by
    nlinarith [hsq1, hsq2, hps0, sq_nonneg (((p : ℝ)) ^ s)]
  have hdenpos : (0 : ℝ) < (((p : ℝ)) ^ s - 1) ^ 2 * ((((p : ℝ)) ^ s - z)) ^ 2 :=
    mul_pos (pow_pos hd1pos 2) (pow_pos hd2pos 2)
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  have hpow : ((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2 ≥ 1 := by
    have hsq : ((((p : ℝ)) ^ s)) ^ 2 = ((p : ℝ)) ^ (2*s) := by
      rw [← Real.rpow_natCast (((p : ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
      norm_num
      ring_nf
    rw [hsq, ← Real.rpow_add hp0]
    calc (1 : ℝ) = ((p : ℝ)) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ ((p : ℝ)) ^ (-(2 : ℝ) + 2*s) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hkey : 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
        * ((4 / 81) * ((((p : ℝ)) ^ s)) ^ 4)
      ≥ 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by
    have hexp : ((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2 ≥ 1 := hpow
    have h4 : ((((p : ℝ)) ^ s)) ^ 4 = ((((p : ℝ)) ^ s)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by ring
    rw [h4]
    have hLQ : (0 : ℝ) ≤ (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by positivity
    have hstep : (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2
          * (((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2)
        ≥ (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hexp hLQ
    calc 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
          * ((4 / 81) * (((((p : ℝ)) ^ s)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2))
        = (800 / 81) * ((Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2
            * (((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2)) := by ring
      _ ≥ (800 / 81) * ((Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 * 1) := by
          apply mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (800 / 81) * ((Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2) := by ring
      _ ≥ 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by nlinarith [hLQ]
  have hmul : 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
        * ((((p : ℝ)) ^ s - 1) ^ 2 * ((((p : ℝ)) ^ s - z)) ^ 2)
      ≥ 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
        * ((4 / 81) * ((((p : ℝ)) ^ s)) ^ 4) := by
    apply mul_le_mul_of_nonneg_left hden
    have : (0 : ℝ) < ((p : ℝ)) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
    positivity
  linarith [hnum, hkey, hmul]

theorem deriv2_clog_prime_term (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ))
          / (((((p : ℝ)) ^ t : ℝ) : ℂ) - 1) / (((((p : ℝ)) ^ t : ℝ) : ℂ) - z))
      ((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2 * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))) s := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (3 : ℝ) ≤ ((p : ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p : ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hpsC : Norm.norm ((((p : ℝ)) ^ s : ℝ) : ℂ) = ((p : ℝ)) ^ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hd1 : ((((p : ℝ)) ^ s : ℝ) : ℂ) - 1 ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    have : ((p : ℝ)) ^ s = 1 := by exact_mod_cast hcon
    linarith
  have hd2 : ((((p : ℝ)) ^ s : ℝ) : ℂ) - z ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    rw [← hcon, hpsC] at hz
    linarith
  have hbase : HasDerivAt (fun t : ℝ => ((((p : ℝ)) ^ t : ℝ) : ℂ))
      (((((p : ℝ)) ^ s * Real.log (p : ℝ) : ℝ)) : ℂ) s :=
    (hasDerivAt_rpow_pos p hp s).ofReal_comp
  have hA : HasDerivAt (fun t : ℝ => ((((p : ℝ)) ^ t : ℝ) : ℂ) - 1)
      (((((p : ℝ)) ^ s * Real.log (p : ℝ) : ℝ)) : ℂ) s := by
    simpa using hbase.sub_const 1
  have hB : HasDerivAt (fun t : ℝ => ((((p : ℝ)) ^ t : ℝ) : ℂ) - z)
      (((((p : ℝ)) ^ s * Real.log (p : ℝ) : ℝ)) : ℂ) s := by
    simpa using hbase.sub_const z
  have hstep1 := (hasDerivAt_const s (-((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ)))).div hA hd1
  have hstep2 := hstep1.div hB hd2
  have hfun : (fun t : ℝ => -((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ))
        / (((((p : ℝ)) ^ t : ℝ) : ℂ) - 1) / (((((p : ℝ)) ^ t : ℝ) : ℂ) - z))
      = (((fun _ : ℝ => -((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ)))
          / fun t : ℝ => ((((p : ℝ)) ^ t : ℝ) : ℂ) - 1)
        / fun t : ℝ => ((((p : ℝ)) ^ t : ℝ) : ℂ) - z) := by
    funext t
    simp only [Pi.div_apply]
  rw [hfun]
  have hval : (z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2 * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))
      = ((0 * (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)
            - -((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ))
              * ((((p : ℝ)) ^ s * Real.log (p : ℝ) : ℝ) : ℂ))
            / (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2 * (((((p : ℝ)) ^ s : ℝ) : ℂ) - z)
          - (((fun _ : ℝ => -((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ)))
              / fun t : ℝ => ((((p : ℝ)) ^ t : ℝ) : ℂ) - 1) s)
              * ((((p : ℝ)) ^ s * Real.log (p : ℝ) : ℝ) : ℂ))
        / (((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2 := by
    simp only [Pi.div_apply]
    push_cast
    field_simp
    ring
  rw [hval]
  exact hstep2

/-- The z-scaled r=2 per-prime derivative, matching the convention of
lemma_3_9_complex's terms (which carry z(z-1), not (z-1)). -/
theorem deriv2_clog_prime_term_z (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -(z * (z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ))
          / (((((p : ℝ)) ^ t : ℝ) : ℂ) - 1) / (((((p : ℝ)) ^ t : ℝ) : ℂ) - z))
      (z * ((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2 * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))) s := by
  have hbase := (deriv2_clog_prime_term p hp s hs z hz).const_mul z
  apply hbase.congr_of_eventuallyEq
  filter_upwards with t
  field_simp

/-- Complex analogue of deriv2_prime_term_bound: the r=2 per-prime derivative
is bounded by 200 log^2 p p^(-2), s-free for s >= 1.
Same crude route: ||z-1|| <= 3, ||(p^s-z)+(p^s-1)|| <= 3p^s,
||p^s-1|| >= (2 / 3)p^s, ||p^s-z|| >= (1 / 3)p^s. -/
theorem deriv2_clog_term_bound (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm ((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2 * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))
      ≤ 200 * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ (-(2 : ℝ))) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hps : (3 : ℝ) ≤ ((p : ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ ((p : ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0 : ℝ) < ((p : ℝ)) ^ s := by linarith
  have hpsC : Norm.norm ((((p : ℝ)) ^ s : ℝ) : ℂ) = ((p : ℝ)) ^ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hps0]
  have hlog0 : (0 : ℝ) ≤ (Real.log (p : ℝ)) ^ 2 := sq_nonneg _
  have hlogC : Norm.norm (((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2) = (Real.log (p : ℝ)) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow,
      abs_of_nonneg (sq_nonneg _)]
  have hz1 : Norm.norm (z - 1) ≤ 3 := by
    calc Norm.norm (z - 1) ≤ Norm.norm z + Norm.norm (1 : ℂ) := norm_sub_le z 1
      _ ≤ 2 + 1 := by simp only [norm_one]; linarith
      _ = 3 := by norm_num
  have hsum3 : Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)
      + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) ≤ 3 * ((p : ℝ)) ^ s := by
    calc Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        ≤ Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z))
          + Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) := norm_add_le _ _
      _ ≤ (((p : ℝ)) ^ s + 2) + (((p : ℝ)) ^ s + 1) := by
          have ha : Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) ≤ ((p : ℝ)) ^ s + 2 := by
            calc Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z))
                ≤ Norm.norm ((((p : ℝ)) ^ s : ℝ) : ℂ) + Norm.norm z := norm_sub_le _ _
              _ ≤ ((p : ℝ)) ^ s + 2 := by rw [hpsC]; linarith
          have hb : Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) ≤ ((p : ℝ)) ^ s + 1 := by
            calc Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
                ≤ Norm.norm ((((p : ℝ)) ^ s : ℝ) : ℂ) + Norm.norm (1 : ℂ) := norm_sub_le _ _
              _ ≤ ((p : ℝ)) ^ s + 1 := by rw [hpsC]; simp only [norm_one]; exact le_refl _
          linarith
      _ ≤ 3 * ((p : ℝ)) ^ s := by linarith
  have hd1 : (2 / 3) * ((p : ℝ)) ^ s ≤ Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) := by
    have h := norm_sub_norm_le ((((p : ℝ)) ^ s : ℝ) : ℂ) (1 : ℂ)
    rw [hpsC] at h
    simp only [norm_one] at h
    linarith
  have hd2 : (1 / 3) * ((p : ℝ)) ^ s ≤ Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) := by
    have h := norm_sub_norm_le ((((p : ℝ)) ^ s : ℝ) : ℂ) z
    rw [hpsC] at h
    linarith
  have hd1p : (0 : ℝ) < Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) := by linarith
  have hd2p : (0 : ℝ) < Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) := by linarith
  rw [norm_div]
  rw [show Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
      * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))
      = Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2
        * Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2 by
    rw [norm_mul, norm_pow, norm_pow]]
  rw [div_le_iff₀ (by positivity)]
  have hnum : Norm.norm ((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2
        * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)))
      ≤ 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hlogC, hpsC]
    calc Norm.norm (z - 1) * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ s
          * Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        ≤ 3 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ s * (3 * ((p : ℝ)) ^ s) := by
          apply mul_le_mul _ hsum3 (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hps0)
          exact mul_le_mul_of_nonneg_right hz1 hlog0
      _ = 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by ring
  have hsq1 : (4 / 9) * ((((p : ℝ)) ^ s)) ^ 2
      ≤ Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2 := by nlinarith [hd1, hps0]
  have hsq2 : (1 / 9) * ((((p : ℝ)) ^ s)) ^ 2
      ≤ Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2 := by nlinarith [hd2, hps0]
  have hden : (4 / 81) * ((((p : ℝ)) ^ s)) ^ 4
      ≤ Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2
        * Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2 := by
    nlinarith [hsq1, hsq2, hps0, sq_nonneg (((p : ℝ)) ^ s)]
  have hpow : ((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2 ≥ 1 := by
    have hsq : ((((p : ℝ)) ^ s)) ^ 2 = ((p : ℝ)) ^ (2*s) := by
      rw [← Real.rpow_natCast (((p : ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
      norm_num
      ring_nf
    rw [hsq, ← Real.rpow_add hp0]
    calc (1 : ℝ) = ((p : ℝ)) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ ((p : ℝ)) ^ (-(2 : ℝ) + 2*s) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hLQ : (0 : ℝ) ≤ (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by positivity
  have hkey : 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
        * ((4 / 81) * ((((p : ℝ)) ^ s)) ^ 4)
      ≥ 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by
    have h4 : ((((p : ℝ)) ^ s)) ^ 4 = ((((p : ℝ)) ^ s)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by ring
    rw [h4]
    have hstep : (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2
          * (((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2)
        ≥ (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hpow hLQ
    calc 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
          * ((4 / 81) * (((((p : ℝ)) ^ s)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2))
        = (800 / 81) * ((Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2
            * (((p : ℝ)) ^ (-(2 : ℝ)) * ((((p : ℝ)) ^ s)) ^ 2)) := by ring
      _ ≥ (800 / 81) * ((Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 * 1) := by
          apply mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (800 / 81) * ((Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2) := by ring
      _ ≥ 9 * (Real.log (p : ℝ)) ^ 2 * ((((p : ℝ)) ^ s)) ^ 2 := by nlinarith [hLQ]
  have hmul : 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
        * (Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1)) ^ 2
          * Norm.norm ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z)) ^ 2)
      ≥ 200 * (Real.log (p : ℝ)) ^ 2 * ((p : ℝ)) ^ (-(2 : ℝ))
        * ((4 / 81) * ((((p : ℝ)) ^ s)) ^ 4) := by
    apply mul_le_mul_of_nonneg_left hden
    have : (0 : ℝ) < ((p : ℝ)) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
    positivity
  linarith [hnum, hkey, hmul]

/-- The z-scaled r=2 bound: ||z|| <= 2 doubles the constant to 400. -/
theorem deriv2_clog_term_bound_z (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm (z * ((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2 * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))))
      ≤ 400 * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ (-(2 : ℝ))) := by
  have hbase := deriv2_clog_term_bound p hp s hs z hz
  have hnn : (0 : ℝ) ≤ 200 * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ (-(2 : ℝ))) := by
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have : (0 : ℝ) < (((p : ℝ)) ^ (-(2 : ℝ))) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  rw [norm_mul]
  calc Norm.norm z * Norm.norm ((z - 1) * ((Real.log (p : ℝ) : ℝ) : ℂ) ^ 2
        * ((((p : ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) + (((((p : ℝ)) ^ s : ℝ) : ℂ) - 1))
        / ((((((p : ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * ((((((p : ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))
      ≤ 2 * (200 * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ (-(2 : ℝ)))) := by
        apply mul_le_mul hz hbase (norm_nonneg _) (by norm_num)
    _ = 400 * (Real.log (p : ℝ)) ^ 2 * (((p : ℝ)) ^ (-(2 : ℝ))) := by ring

/-- The r=2 s-free dominator, indexed at p >= 5.
Rebuilt from the N-indexed p-series rather than restricted from the p >= 3
version, per the file's idiom. -/
theorem deriv2_bound_uniform_summable_five :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      200 * (Real.log ((p : ℕ):ℝ)) ^ 2 * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 : ℝ)/4)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (((p : ℕ):ℝ)) ^ (-(5 : ℝ)/4)) := hbase.subtype _
  have hc := hsub.mul_left ((200 : ℝ) * (64 / 9))
  apply Summable.of_nonneg_of_le _ _ hc
  · intro p
    have hp5 : (5 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have : (0 : ℝ) ≤ (Real.log ((p : ℕ):ℝ)) ^ 2 := sq_nonneg _
    positivity
  · intro p
    have hp5 : (5 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
    have hlog := log_sq_le (((p : ℕ):ℝ)) (by linarith)
    have hpos : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
    have hstep : (Real.log ((p : ℕ):ℝ)) ^ 2 * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        ≤ ((64 / 9) * (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4)) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    have hcomb : ((64 / 9) * (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4)) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        = (64 / 9) * (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4 + -(2 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hp0]
    have hmono : (((p : ℕ):ℝ)) ^ ((3 : ℝ)/4 + -(2 : ℝ)) ≤ (((p : ℕ):ℝ)) ^ (-(5 : ℝ)/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      norm_num
    rw [hcomb] at hstep
    nlinarith [hstep, hmono, hpos, sq_nonneg (Real.log ((p : ℕ):ℝ))]

/-- The r=2 dominator at constant 400, for the z-scaled terms. -/
theorem deriv2_bound_uniform_summable_five_z :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      400 * (Real.log ((p : ℕ):ℝ)) ^ 2 * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))) := by
  have h := deriv2_bound_uniform_summable_five.mul_left 2
  apply h.congr
  intro p
  ring

/-- Complex analogue of deriv_log_one_sub_const_rpow:
d/ds Complex.log(1 - c*p^(-s)) = c*log p*p^(-s)/(1 - c*p^(-s)) for complex c.
The inner function is real-valued (the exponent is real), so its derivative
comes from hasDerivAt_rpow_neg cast to C; only the outer log is complex, and
one_sub_mem_slitPlane supplies its side condition. -/
theorem deriv_clog_one_sub_const_rpow (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (c : ℂ) (hc : Norm.norm c ≤ 2) :
    HasDerivAt (fun t : ℝ => Complex.log (1 - c * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)))
      (c * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) * ((((((p : ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
        / (1 - c * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))) s := by
  have hslit := one_sub_mem_slitPlane p hp s hs c hc
  have hreal := hasDerivAt_rpow_neg p hp s
  have hcast : HasDerivAt (fun t : ℝ => (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
      (((-((((p : ℕ):ℝ)) ^ (-s) * Real.log ((p : ℕ):ℝ)) : ℝ) : ℂ)) s :=
    hreal.ofReal_comp
  have hin : HasDerivAt (fun t : ℝ => 1 - c * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
      (c * (((((((p : ℕ):ℝ)) ^ (-s) * Real.log ((p : ℕ):ℝ)) : ℝ)) : ℂ)) s := by
    have h := (hcast.const_mul c).const_sub 1
    have hval : c * (((((((p : ℕ):ℝ)) ^ (-s) * Real.log ((p : ℕ):ℝ)) : ℝ)) : ℂ)
        = -(c * ((-((((p : ℕ):ℝ)) ^ (-s) * Real.log ((p : ℕ):ℝ)) : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hval]
    exact h
  have h := (Complex.hasDerivAt_log hslit).scomp s hin
  simp only [Function.comp_def, smul_eq_mul] at h
  have hne : (1 : ℂ) - c * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ) ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  have hval : c * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ)
        * ((((((p : ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
        / (1 - c * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))
      = c * (((((((p : ℕ):ℝ)) ^ (-s) * Real.log ((p : ℕ):ℝ)) : ℝ)) : ℂ)
        * (1 - c * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ := by
    push_cast
    field_simp
  rw [hval]
  exact h

/-- Complex per-prime term of Lemma 3.9:
d/ds [-Complex.log(1 - z p^(-s)) + z Complex.log(1 - p^(-s))]
  = -z(z-1) log p / ((p^s - 1)(p^s - z)).
Complex analogue of deriv_log_prime_factor; the cancellation between the two
logs is again what produces the p^(-2s) decay. -/
theorem deriv_clog_prime_factor (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * Complex.log (1 - (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)))
      (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)) s := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have hps : (3 : ℝ) ≤ (((p : ℕ):ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p : ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hneg : (((p : ℕ):ℝ)) ^ (-s) = ((((p : ℕ):ℝ)) ^ s)⁻¹ := Real.rpow_neg (le_of_lt hp0) s
  have hone : Norm.norm (1 : ℂ) ≤ 2 := by simp
  have hA := (deriv_clog_one_sub_const_rpow p hp s hs z hz).neg
  have hB := (deriv_clog_one_sub_const_rpow p hp s hs 1 hone).const_mul z
  simp only [one_mul] at hB
  have hsum := hA.add hB
  have hslitz := Complex.slitPlane_ne_zero (one_sub_mem_slitPlane p hp s hs z hz)
  have hslit1 := Complex.slitPlane_ne_zero (one_sub_mem_slitPlane p hp s hs 1 hone)
  simp only [one_mul] at hslit1
  have hpsC : (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro hcon
    rw [hcon] at hps
    linarith
  have hval : -(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)
      = -(z * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ)
            * ((((((p : ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
            / (1 - z * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ)))
        + z * (((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ)
            * ((((((p : ℕ):ℝ)) ^ (-s) : ℝ)) : ℂ)
            / (1 - (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))) := by
    rw [hneg]
    rw [Complex.ofReal_inv]
    rw [show (1 : ℂ) - z * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ))⁻¹
        = (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - z) / ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) by
      field_simp]
    rw [show (1 : ℂ) - ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ))⁻¹
        = (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - 1) / ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) by
      field_simp]
    have hz1 : ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - z ≠ 0 := by
      intro hcon
      rw [sub_eq_zero] at hcon
      rw [← hcon] at hz
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ((p : ℕ):ℝ) ^ s)] at hz
      linarith
    have hz2 : ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - 1 ≠ 0 := by
      intro hcon
      rw [sub_eq_zero] at hcon
      have : ((((p : ℕ):ℝ)) ^ s : ℝ) = 1 := by exact_mod_cast hcon
      linarith
    field_simp
    ring
  rw [hval]
  exact hsum

/-- Complex analogue of deriv_prime_term_bound_uniform: the s-free dominating
bound for the per-prime derivative.  Same constant 27, same crude route, with
norms in place of absolute values. -/
theorem deriv_clog_term_bound_uniform (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
      ≤ 27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have hps : (3 : ℝ) ≤ (((p : ℕ):ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p : ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hps0 : (0 : ℝ) < (((p : ℕ):ℝ)) ^ s := by linarith
  have hlogpos : (0 : ℝ) ≤ Real.log ((p : ℕ):ℝ) := Real.log_nonneg (by linarith)
  have hnum : Norm.norm (z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
      ≤ 6 * Real.log ((p : ℕ):ℝ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogpos]
    have h1 : Norm.norm (z - 1) ≤ 3 := by
      calc Norm.norm (z - 1) ≤ Norm.norm z + Norm.norm (1 : ℂ) := norm_sub_le z 1
        _ ≤ 2 + 1 := by simp only [norm_one]; linarith
        _ = 3 := by norm_num
    have hprod6 : Norm.norm z * Norm.norm (z - 1) ≤ 6 := by
      nlinarith [norm_nonneg z, norm_nonneg (z - 1), hz, h1]
    nlinarith [hprod6, hlogpos]
  have hd1 : (2 / 3) * (((p : ℕ):ℝ)) ^ s
      ≤ Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1) := by
    have hre : ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)
        = (((((((p : ℕ):ℝ)) ^ s - 1 : ℝ))) : ℂ) := by push_cast; ring
    rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hd2 : (1 / 3) * (((p : ℕ):ℝ)) ^ s
      ≤ Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z) := by
    have hge : Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z)
        ≥ Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ))) - Norm.norm z :=
      norm_sub_norm_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hps0] at hge
    linarith
  rw [norm_div, norm_div]
  rw [div_div]
  have hdpos : (0 : ℝ) < Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)
      * Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z) := by
    have h1 : (0 : ℝ) < Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1) := by
      linarith [hd1, hps0]
    have h2 : (0 : ℝ) < Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z) := by
      linarith [hd2, hps0]
    positivity
  rw [div_le_iff₀ hdpos]
  have hprod : (2 / 9) * ((((p : ℕ):ℝ)) ^ s) ^ 2
      ≤ Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)
          * Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z) := by
    nlinarith [hd1, hd2, hps0, norm_nonneg ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)]
  rw [norm_neg]
  have hkey : 27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        * ((2 / 9) * ((((p : ℕ):ℝ)) ^ s) ^ 2)
      ≥ 6 * Real.log ((p : ℕ):ℝ) := by
    have hsq : ((((p : ℕ):ℝ)) ^ s) ^ 2 = (((p : ℕ):ℝ)) ^ (2*s) := by
      rw [← Real.rpow_natCast ((((p : ℕ):ℝ)) ^ s) 2, ← Real.rpow_mul (le_of_lt hp0)]
      norm_num
      ring_nf
    rw [hsq]
    have hge : (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) * (((p : ℕ):ℝ)) ^ (2*s) ≥ 1 := by
      rw [← Real.rpow_add hp0]
      have hexp : (0 : ℝ) ≤ -(2 : ℝ) + 2*s := by linarith
      calc (1 : ℝ) = (((p : ℕ):ℝ)) ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ (((p : ℕ):ℝ)) ^ (-(2 : ℝ) + 2*s) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    nlinarith [hge, hlogpos]
  have hmul : 27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        * (Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - 1)
          * Norm.norm ((((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ)) - z))
      ≥ 27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        * ((2 / 9) * ((((p : ℕ):ℝ)) ^ s) ^ 2) := by
    have hc : (0 : ℝ) ≤ 27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := by
      have : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
      positivity
    exact mul_le_mul_of_nonneg_left hprod hc
  linarith [hnum, hkey, hmul]

/-- File-canonical form of the complex per-prime derivative: second term as a
real log cast to C (matching G2tailC_eq_exp_sum and
prime_correction_summable_complex), indexed from p >= 5 to match G2tailC. -/
theorem deriv_clog_prime_factor_canon (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    HasDerivAt (fun t : ℝ =>
        -Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ))
      (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)) s := by
  have hbase := deriv_clog_prime_factor p hp s hs z hz
  apply hbase.congr_of_eventuallyEq
  have hnhds : Set.Ioi (0 : ℝ) ∈ nhds s := by
    apply Ioi_mem_nhds
    linarith
  filter_upwards [hnhds] with t ht
  congr 1
  congr 1
  have hpr : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have ht0 : (0 : ℝ) < t := ht
  have hlt : (((p : ℕ):ℝ)) ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hpos : (0 : ℝ) < 1 - (((p : ℕ):ℝ)) ^ (-t) := by linarith
  rw [Complex.ofReal_log (le_of_lt hpos)]
  push_cast
  ring

/-- The s-free dominator, indexed over p >= 5 to match G2tailC.
Rebuilt from the N-indexed p-series rather than restricted from the p >= 3
version: those are different subtypes of N, neither contained in the other as
Lean sees it, and the file's idiom (line ~1126) is to restrict from N. -/
theorem deriv_bound_uniform_summable_five :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      27 * Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ)/2)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      (((p : ℕ):ℝ)) ^ (-(3 : ℝ)/2)) := hbase.subtype _
  have h27 := hsub.mul_left 27
  apply Summable.of_nonneg_of_le _ _ h27
  · intro p
    have hp5 : (5 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have : (0 : ℝ) ≤ Real.log ((p : ℕ):ℝ) := Real.log_nonneg (by linarith)
    positivity
  · intro p
    have hp5 : (5 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast p.2.2
    have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
    have hlog := log_le_sqrt (((p : ℕ):ℝ)) (by linarith)
    have hpos : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
    have hstep : Real.log ((p : ℕ):ℝ) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        ≤ ((((p : ℕ):ℝ)) ^ ((1 : ℝ)/2)) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (le_of_lt hpos)
    have hcomb : ((((p : ℕ):ℝ)) ^ ((1 : ℝ)/2)) * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))
        = (((p : ℕ):ℝ)) ^ (-(3 : ℝ)/2) := by
      rw [← Real.rpow_add hp0]
      norm_num
    rw [hcomb] at hstep
    nlinarith [hstep]

/-- The p >= 5 series in cBracket converges at s = 1.
Needed for cBracket f1 1 z to be a genuine value rather than a tsum junk
value: at s = 1 the terms are -z(z-1)log p/((p-1)(p-z)), which is O(log p/p^2). -/
theorem cBracket_series_summable_at_one (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      -(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / ((((((p : ℕ):ℝ)) ^ (1 : ℝ) : ℝ) : ℂ) - 1)
          / ((((((p : ℕ):ℝ)) ^ (1 : ℝ) : ℝ) : ℂ) - z)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    _ deriv_bound_uniform_summable_five
  intro p
  exact deriv_clog_term_bound_uniform (p : ℕ) (by omega) 1 (le_refl 1) z hz

/-- Per-term s-continuity for cBracket's series on {s // 1 <= s}.
The denominators are nonvanishing there: p^s - 1 >= 2 and |p^s - z| >= 1
since p^s >= 3 and ||z|| <= 2. -/
theorem cBracket_term_continuous_s (p : ℕ) (hp : 3 ≤ p) (z : ℂ)
    (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      -(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ) - z)) := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have hsub : Continuous (fun s : {s : ℝ // 1 ≤ s} => (s : ℝ)) := continuous_subtype_val
  have hrpow : Continuous (fun s : {s : ℝ // 1 ≤ s} => (((p : ℕ):ℝ)) ^ (s : ℝ)) :=
    (continuous_const_rpow (ne_of_gt hp0)).comp hsub
  have hps : ∀ s : {s : ℝ // 1 ≤ s}, (3 : ℝ) ≤ (((p : ℕ):ℝ)) ^ (s : ℝ) := by
    intro s
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) s.2
      _ ≤ (((p : ℕ):ℝ)) ^ (s : ℝ) := Real.rpow_le_rpow (by norm_num) hp3 (by linarith [s.2])
  have hcast : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ))) := Complex.continuous_ofReal.comp hrpow
  have hd1 : ∀ s : {s : ℝ // 1 ≤ s},
      (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ)) - 1 ≠ 0 := by
    intro s hcon
    rw [sub_eq_zero] at hcon
    have : ((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ) = 1 := by exact_mod_cast hcon
    linarith [hps s]
  have hd2 : ∀ s : {s : ℝ // 1 ≤ s},
      (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ)) - z ≠ 0 := by
    intro s hcon
    rw [sub_eq_zero] at hcon
    rw [← hcon, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hps s] : (0 : ℝ) < (((p : ℕ):ℝ)) ^ (s : ℝ))] at hz
    linarith [hps s]
  exact ((continuous_const.div (hcast.sub continuous_const) hd1).div
    (hcast.sub continuous_const) hd2)

/-- cBracket's series is s-continuous on {s // 1 <= s}. -/
theorem cBracket_series_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ) - 1)
            / (((((((p : ℕ):ℝ)) ^ (s : ℝ) : ℝ)) : ℂ) - z))) := by
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      cBracket_term_continuous_s (p : ℕ) (by omega) z hz)
    deriv_bound_uniform_summable_five
  intro p s
  exact deriv_clog_term_bound_uniform (p : ℕ) (by omega) (s : ℝ) s.2 z hz

/-- MANUSCRIPT Theorem 6.1: bHat_i = [z^i] G2^(1,0)(1,z).
Defined through the explicit s = 1 product G2at1 z * cBracket f1 1 z rather
than by evaluating G2manu at s = 1, which is a junk value (kappaFac 1 = 0).
f1 = f 1 is the log-derivative of zetaTilde at 1; the manuscript has
f(1) = -gamma via the Stieltjes expansion, certified from FLINT. -/
theorem deriv2_series_summable_at_basepoint (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      -(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / ((((((p : ℕ):ℝ)) ^ (3 / 2:ℝ) : ℝ) : ℂ) - 1)
        / ((((((p : ℕ):ℝ)) ^ (3 / 2:ℝ) : ℝ) : ℂ) - z)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    _ (deriv_bound_uniform_summable_five)
  intro p
  exact deriv_clog_term_bound_uniform (p : ℕ) (by omega) (3 / 2) (by norm_num) z hz


theorem hasDerivAt_clog_series2 (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
          / ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
          / ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - z)))
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (z * ((z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2
            * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
            * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z
              + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
          / (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
            * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))))) s := by
  have hy0 : (3 / 2 : ℝ) ∈ Set.Ioo (1 : ℝ) 2 := by
    constructor <;> norm_num
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun (p : {p : ℕ // p.Prime ∧ 5 ≤ p}) (t : ℝ) =>
      -(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
        / ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - z))
    (g' := fun (p : {p : ℕ // p.Prime ∧ 5 ≤ p}) (t : ℝ) =>
      z * ((z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2
          * (((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ)
          * ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - z
            + ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1))
        / (((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1) ^ 2
          * (((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - z) ^ 2))))
    deriv2_bound_uniform_summable_five_z isOpen_Ioo isPreconnected_Ioo
    _ _ hy0 (deriv2_series_summable_at_basepoint z hz) hsmem
  · intro p y hy
    exact deriv2_clog_prime_term_z (p : ℕ) (by omega) y (le_of_lt hy.1) z hz
  · intro p y hy
    exact deriv2_clog_term_bound_z (p : ℕ) (by omega) y (le_of_lt hy.1) z hz


/-- The derivative of Lemma 3.9's bracket C(s) = z c(s,z).
Sum of the kappa-part, the p = 3 term, and the tail series. -/
theorem hasDerivAt_c_bracket (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) (f fp : ℝ → ℝ)
    (hfp : HasDerivAt f (fp s) s) :
    HasDerivAt (fun t : ℝ =>
        z * (((f t + Real.log 2 / ((2 : ℝ) ^ t - 1) : ℝ)) : ℂ)
          + ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
              / ((((((3 : ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
                / ((((((3 : ℕ):ℝ)) ^ t : ℝ) : ℂ) - z))
            + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                  / ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - 1)
                    / ((((((p : ℕ):ℝ)) ^ t : ℝ) : ℂ) - z))))
      (z * (((fp s + -((Real.log 2) ^ 2 * (2 : ℝ) ^ s) / ((2 : ℝ) ^ s - 1) ^ 2 : ℝ)) : ℂ)
        + ((z * ((z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ) ^ 2
              * (((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ)
              * ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z
                + ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
            / (((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
              * (((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2))))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (z * ((z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2
                  * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
                  * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z
                    + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
                / (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
                  * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z) ^ 2)))))) s := by
  have hkp := hasDerivAt_kappa_part z s hsmem f fp hfp
  have hp3 := deriv2_clog_prime_term_z 3 (le_refl 3) s (le_of_lt hsmem.1) z hz
  have htail := hasDerivAt_clog_series2 z hz s hsmem
  exact hkp.add (hp3.add htail)

/-- MANUSCRIPT section 6.1's input: G2^(2,0) = G2 * (C^2 + C'), where C = z c.
This is the manuscript's G2(z^2 c^2 + z c') -- "a formula derived, not read:
differentiate d_s G2 = z c G2 once more".
Both f and its derivative fp are hypotheses, as in Lemma 3.9. -/
theorem hasDerivAt_G2manu_second (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) (f fp : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x)
    (hfp : HasDerivAt f (fp s) s)
    (C : ℝ → ℂ) (Cp : ℂ)
    (hC : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => G2manu t z) (G2manu x z * C x) x)
    (hCp : HasDerivAt C Cp s) :
    HasDerivAt (fun t : ℝ => G2manu t z * C t)
      (G2manu s z * C s * C s + G2manu s z * Cp) s := by
  have hG2 := hC s hsmem
  exact hG2.mul hCp

/-- Basepoint summability at s = 3 / 2 over p >= 5, for the complex log-series.
Same shape as prime_factor_sub_one_summable: restrict the N-indexed p-series,
then compare termwise against prime_correction_bound_complex. -/
theorem clog_series_summable_at_basepoint (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      -Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-(3 / 2:ℝ)) : ℝ) : ℂ))
        + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-(3 / 2:ℝ))) : ℝ) : ℂ)) := by
  have hcomp : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      18 * (((p : ℕ):ℝ)) ^ (-2*(3 / 2:ℝ))) := by
    have h2s : -(2*(3 / 2:ℝ)) < -1 := by norm_num
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2*(3 / 2:ℝ)))) :=
      Real.summable_nat_rpow.mpr h2s
    have hsub : Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
        (((p : ℕ):ℝ)) ^ (-(2*(3 / 2:ℝ)))) := hbase.subtype _
    have heq : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (18 : ℝ) * (((p : ℕ):ℝ)) ^ (-2*(3 / 2:ℝ))
          = 18 * (((p : ℕ):ℝ)) ^ (-(2*(3 / 2:ℝ))) := by
      intro p; ring_nf
    simp_rw [heq]
    exact hsub.mul_left 18
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} => norm_nonneg _)
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      prime_correction_bound_complex (p : ℕ) (by omega) (3 / 2) (by norm_num) z hz)
    hcomp

/-- Termwise differentiation of the complex p >= 5 log-series.
Complex analogue of hasDerivAt_log_series; hasDerivAt_tsum_of_isPreconnected
takes F in any complete normed space, so C works unchanged. -/
theorem hasDerivAt_clog_series (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ)))
      (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) s := by
  have hy0 : (3 / 2 : ℝ) ∈ Set.Ioo (1 : ℝ) 2 := by
    constructor <;> norm_num
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun (p : {p : ℕ // p.Prime ∧ 5 ≤ p}) (t : ℝ) =>
      -Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
        + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ))
    (g' := fun (p : {p : ℕ // p.Prime ∧ 5 ≤ p}) (t : ℝ) =>
      -(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ t : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ t : ℝ)) : ℂ) - z))
    deriv_bound_uniform_summable_five isOpen_Ioo isPreconnected_Ioo
    _ _ hy0 (clog_series_summable_at_basepoint z hz) hsmem
  · intro p y hy
    exact deriv_clog_prime_factor_canon (p : ℕ) (by omega) y (le_of_lt hy.1) z hz
  · intro p y hy
    exact deriv_clog_term_bound_uniform (p : ℕ) (by omega) y (le_of_lt hy.1) z hz

/-- d/ds G2tailC = G2tailC * (sum of per-prime derivatives).
The key step of the complex chain: G2tailC is exp of the log-series
(G2tailC_eq_exp_sum), so differentiating goes through HasDerivAt.cexp and
never requires Complex.log of the product -- which would be false in general
because of branch cuts. -/
theorem hasDerivAt_G2tailC (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => G2tailC t z)
      (G2tailC s z * ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) s := by
  have hser := hasDerivAt_clog_series z hz s hsmem
  have hexp := hser.cexp
  have heq : ∀ t : ℝ, t ∈ Set.Ioo (1 : ℝ) 2 →
      Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ)))
      = G2tailC t z := by
    intro t ht
    exact (G2tailC_eq_exp_sum t (le_of_lt ht.1) z hz).symm
  have hval : Complex.exp (∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-s)) : ℝ) : ℂ)))
      = G2tailC s z := heq s hsmem
  rw [← hval]
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact (heq t ht).symm

/-- d/ds of the p = 3 Euler factor, via exp of its log.
Same route as hasDerivAt_G2tailC applied to a single term:
prime_factor_eq_exp_complex expresses the factor as exp(correction), and
deriv_clog_prime_factor_canon (now at p >= 3) differentiates the exponent. -/
theorem hasDerivAt_prime_three_factor (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ =>
        (1 - z * (((((3 : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ))⁻¹
          * (((1 - (((3 : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z)
      (((1 - z * (((((3 : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹
          * (((1 - (((3 : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ)) ^ z)
        * (-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
            / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
              / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) s := by
  have hder := deriv_clog_prime_factor_canon 3 (le_refl 3) s (le_of_lt hsmem.1) z hz
  have hexp := hder.cexp
  have heq : ∀ t : ℝ, t ∈ Set.Ioo (1 : ℝ) 2 →
      Complex.exp (-Complex.log (1 - z * ((((((3 : ℕ):ℝ)) ^ (-t) : ℝ)) : ℂ))
          + z * ((Real.log (1 - (((3 : ℕ):ℝ)) ^ (-t)) : ℝ) : ℂ))
        = (1 - z * ((((((3 : ℕ):ℝ)) ^ (-t) : ℝ)) : ℂ))⁻¹
            * (((1 - (((3 : ℕ):ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z := by
    intro t ht
    exact (prime_factor_eq_exp_complex 3 (le_refl 3) t (le_of_lt ht.1) z hz).symm
  rw [← heq s hsmem]
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact (heq t ht).symm

/-- d/ds G2C = G2C * (per-prime sum over p >= 3), assembling the p = 3 factor
and the p >= 5 tail by the product rule.  The p = 3 term appears separately
because G2C splits it out; combining gives the full p >= 3 sum of Lemma 3.9. -/
theorem hasDerivAt_G2C (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => G2C t z)
      (G2C s z *
        ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
            / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
              / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)))) s := by
  have h3 := hasDerivAt_prime_three_factor z hz s hsmem
  have htail := hasDerivAt_G2tailC z hz s hsmem
  have hcast : ∀ t : ℝ, ((((3 : ℕ):ℝ)) ^ (-t) : ℝ) = (((3 : ℝ)) ^ (-t) : ℝ) := by
    intro t
    norm_num
  simp only [hcast] at h3
  have hmul := h3.mul htail
  have hG2C : ∀ t : ℝ, G2C t z
      = ((1 - z * ((((3 : ℝ)) ^ (-t) : ℝ) : ℂ))⁻¹
          * (((1 - ((3 : ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z) * G2tailC t z := by
    intro t
    unfold G2C
    ring
  have hfun : (fun t : ℝ => G2C t z)
      = ((fun t : ℝ => (1 - z * ((((3 : ℝ)) ^ (-t) : ℝ) : ℂ))⁻¹
          * (((1 - ((3 : ℝ)) ^ (-t) : ℝ) : ℂ)) ^ z) * fun t : ℝ => G2tailC t z) := by
    funext t
    simp only [Pi.mul_apply]
    exact hG2C t
  rw [hfun]
  have hval : G2C s z *
      ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
          / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
        + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
            (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
              / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)))
      = (1 - z * ((((3 : ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - ((3 : ℝ)) ^ (-s) : ℝ) : ℂ)) ^ z
          * (-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
              / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)) * G2tailC s z
        + (1 - z * ((((3 : ℝ)) ^ (-s) : ℝ) : ℂ))⁻¹ * (((1 - ((3 : ℝ)) ^ (-s) : ℝ) : ℂ)) ^ z
          * (G2tailC s z * ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))) := by
    rw [hG2C s]
    ring
  rw [hval]
  exact hmul

/-- d/ds of kappa(t)^z: the cpow of a positive real function, differentiated
via exp(z log kappa).  Gives kappa^z * z * (log kappa)', and
(log kappa)' = f(s) + log 2/(2^s - 1) by kappaFac_eq_zetaTilde. -/
theorem hasDerivAt_kappa_cpow (z : ℂ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1 : ℝ) 2)
    (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ => ((kappaFac t : ℝ) : ℂ) ^ z)
      (((kappaFac s : ℝ) : ℂ) ^ z
        * (z * (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ))) s := by
  have hs1 : 1 < s := hsmem.1
  have hklog : HasDerivAt (fun t : ℝ => Real.log (kappaFac t))
      (f s + Real.log 2 / ((2 : ℝ) ^ s - 1)) s := by
    have hsplit : ∀ t : ℝ, t ∈ Set.Ioo (1 : ℝ) 2 →
        Real.log (kappaFac t) = Real.log (zetaTilde t) + Real.log (1 - (2 : ℝ) ^ (-t)) := by
      intro t ht
      rw [kappaFac_eq_zetaTilde t ht.1,
        Real.log_mul (ne_of_gt (zetaTilde_pos t ht.1)) (ne_of_gt (one_sub_two_pow_pos t ht.1))]
    have hsum := hf.add (deriv_log_one_sub_two_pow s hs1)
    apply hsum.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
    simp only [Pi.add_apply]
    exact hsplit t ht
  have hcast : HasDerivAt (fun t : ℝ => ((Real.log (kappaFac t) : ℝ) : ℂ))
      (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ) : ℂ)) s := hklog.ofReal_comp
  have hmul : HasDerivAt (fun t : ℝ => z * ((Real.log (kappaFac t) : ℝ) : ℂ))
      (z * (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)) s := hcast.const_mul z
  have hexp := hmul.cexp
  have heq : ∀ t : ℝ, t ∈ Set.Ioo (1 : ℝ) 2 →
      Complex.exp (z * ((Real.log (kappaFac t) : ℝ) : ℂ)) = ((kappaFac t : ℝ) : ℂ) ^ z := by
    intro t ht
    have hkpos : 0 < kappaFac t := kappaFac_pos t ht.1 (cFac_pos t ht.1)
    rw [ofReal_cpow_eq_exp (kappaFac t) hkpos z]
  rw [← heq s hsmem]
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsmem.1 hsmem.2] with t ht
  exact (heq t ht).symm

/-- MANUSCRIPT LEMMA 3.9 (complex z): G2^(1,0) = z * G2 * c(s,z), with
  c(s,z) = log 2/(2^s - 1) + f(s) - sum_{p>=3} (z-1) log p/((p^s-1)(p^s-z)).
Stated in the multiplied form the manuscript's section 3.5 uses (G2^(1,0) =
z G2 c), not the logarithmic one -- that avoids Complex.log of the product,
which branch cuts would break.

f is a hypothesis, as in lemma_3_9_real: the manuscript certifies it
numerically from FLINT Stieltjes constants rather than expanding it. -/
theorem lemma_3_9_complex (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ => G2manu t z)
      (G2manu s z *
        (z * (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)
          + ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
              / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
            + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                  / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                    / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))))) s := by
  have hkap := hasDerivAt_kappa_cpow z s hsmem f hf
  have hg2c := hasDerivAt_G2C z hz s hsmem
  have hmul := hkap.mul hg2c
  have hfun : (fun t : ℝ => G2manu t z)
      = ((fun t : ℝ => ((kappaFac t : ℝ) : ℂ) ^ z) * fun t : ℝ => G2C t z) := by
    funext t
    simp only [Pi.mul_apply]
    unfold G2manu
    ring
  rw [hfun]
  have hval : G2manu s z *
      (z * (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)
        + ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
            / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
              / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))))
      = ((kappaFac s : ℝ) : ℂ) ^ z
          * (z * (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)) * G2C s z
        + ((kappaFac s : ℝ) : ℂ) ^ z
          * (G2C s z *
            ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
                / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z))
              + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                  (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                    / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                      / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - z)))) := by
    unfold G2manu
    ring
  rw [hval]
  exact hmul

/-- Lemma 3.9's bracket C(s,z) = z c(s,z), as a function of s and z.
Naming it lets the s -> 1 limit and the coefficient extraction be stated
without repeating the three-part expression. f is the log-derivative of
zetaTilde, carried as a parameter. -/
noncomputable def cBracket (fs : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  z * (((fs + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)
    + ((-(z * (z - 1) * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
        / ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
          / ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z))
      + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
          (-(z * (z - 1) * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
            / ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
              / ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - z)))

/-- cBracket is affine in its first argument: cBracket fs s z - cBracket gs s z
= z * (fs - gs).  This is what lets the two-argument limit
cBracket (f s) s z -> cBracket f1 1 z split into f's convergence and the
fixed-fs limit. -/
theorem cBracket_sub_first (fs gs s : ℝ) (z : ℂ) :
    cBracket fs s z - cBracket gs s z = z * (((fs - gs : ℝ)) : ℂ) := by
  unfold cBracket
  push_cast
  ring

theorem cBracket_continuous_s (fs : ℝ) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} => cBracket fs (s : ℝ) z) := by
  have hsub : Continuous (fun s : {s : ℝ // 1 ≤ s} => (s : ℝ)) := continuous_subtype_val
  have hrpow2 : Continuous (fun s : {s : ℝ // 1 ≤ s} => (2 : ℝ) ^ (s : ℝ)) :=
    (continuous_const_rpow (by norm_num)).comp hsub
  have h2ge : ∀ s : {s : ℝ // 1 ≤ s}, (2 : ℝ) ≤ (2 : ℝ) ^ (s : ℝ) := by
    intro s
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) s.2
  have hne : ∀ s : {s : ℝ // 1 ≤ s}, (2 : ℝ) ^ (s : ℝ) - 1 ≠ 0 := by
    intro s hcon
    linarith [h2ge s]
  have hkap : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      z * (((fs + Real.log 2 / ((2 : ℝ) ^ (s : ℝ) - 1) : ℝ)) : ℂ)) := by
    apply continuous_const.mul
    apply Complex.continuous_ofReal.comp
    exact continuous_const.add (continuous_const.div (hrpow2.sub continuous_const) hne)
  unfold cBracket
  apply hkap.add
  apply Continuous.add
  · exact cBracket_term_continuous_s 3 (le_refl 3) z hz
  · exact cBracket_series_continuous_s z hz


/-- cBracket fs s z -> cBracket fs 1 z as s -> 1 from above.
Same bridge as G2C_tendsto_at_one: continuity on the subtype {s // 1 <= s}
gives the limit along nhdsWithin 1 (Ici 1), and nhdsWithin 1 (Ioi 1) is finer. -/
theorem cBracket_tendsto_at_one (fs : ℝ) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Filter.Tendsto (fun s : ℝ => cBracket fs s z) (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (cBracket fs 1 z)) := by
  have hmem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (le_refl 1)
  have hcont := cBracket_continuous_s fs z hz
  have hsub : Filter.Tendsto ((Set.Ici (1 : ℝ)).restrict (fun s : ℝ => cBracket fs s z))
      (nhds (⟨(1 : ℝ), hmem⟩ : ↑(Set.Ici (1 : ℝ)))) (nhds (cBracket fs 1 z)) := by
    exact hcont.continuousAt
  have hIci := (tendsto_nhdsWithin_iff_subtype hmem (fun s : ℝ => cBracket fs s z)
    (nhds (cBracket fs 1 z))).mpr hsub
  apply hIci.mono_left
  apply nhdsWithin_mono
  intro x hx
  exact le_of_lt (Set.mem_Ioi.mp hx)

/-- The two-argument limit: cBracket (f s) s z -> cBracket f1 1 z as s -> 1+.
Splits via cBracket_sub_first into f's convergence and the fixed-fs limit. -/
theorem cBracket_tendsto_two_arg (z : ℂ) (hz : Norm.norm z ≤ 2)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds f1)) :
    Filter.Tendsto (fun s : ℝ => cBracket (f s) s z)
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (cBracket f1 1 z)) := by
  have hfix := cBracket_tendsto_at_one f1 z hz
  have hdiff : Filter.Tendsto (fun s : ℝ => z * (((f s - f1 : ℝ)) : ℂ))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds 0) := by
    have hz0 : Filter.Tendsto (fun s : ℝ => ((f s - f1 : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds 0) := by
      have hs : Filter.Tendsto (fun s : ℝ => f s - f1)
          (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (f1 - f1)) :=
        hfc.sub (tendsto_const_nhds (x := f1))
      rw [sub_self] at hs
      exact (Complex.continuous_ofReal.continuousAt).tendsto.comp hs
    have := hz0.const_mul z
    simpa using this
  have hsum := hdiff.add hfix
  simp only [zero_add] at hsum
  apply hsum.congr
  intro s
  have h := cBracket_sub_first (f s) f1 s z
  rw [← h]
  ring

noncomputable def G2deriv1 (f1 : ℝ) (z : ℂ) : ℂ := G2at1 z * cBracket f1 1 z

/-- MANUSCRIPT Theorem 6.1: bHat_i = [z^i] G2^(1,0)(1,z), as a contour
integral at radius 2 rather than as a Taylor coefficient.

The contour form is what the Taylor argument consumes, and it avoids needing
z-analyticity of cBracket: the s -> 1 limit is taken under the integral by
dominated convergence, exactly as gManu_tendsto_cCoeff does for cCoeff. -/
noncomputable def bHat (f1 : ℝ) (i : ℕ) : ℂ :=
  (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
    • (circleIntegral (fun z : ℂ => (1 / z) ^ i • z⁻¹ • G2deriv1 f1 z) 0 (2 : ℝ))


/-- Per-term split for Theorem 6.1: the Dk integrand decomposes into the
(s-1)-weighted bHat term plus a remainder bounded by gh_i (s-1)^2 / 2. -/
theorem Dk_term_split (i j l : ℕ) (f1 : ℝ) (gh_i : ℝ) (hgh0 : 0 ≤ gh_i)
    (htaylor : ∀ s ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (gManu i s - cCoeff i - (((s - 1 : ℝ)) : ℂ) * bHat f1 i)
        ≤ gh_i * (s - 1) ^ 2 / 2)
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    |((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))
      - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))|
      ≤ gh_i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) := by
  have hL : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  have hW : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℝ) * s)
      * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)) := by positivity
  have hre : ((gManu i s).re - (cCoeff i).re) - (bHat f1 i).re * (s - 1)
      = (gManu i s - cCoeff i - (((s - 1 : ℝ)) : ℂ) * bHat f1 i).re := by
    simp [Complex.sub_re, Complex.mul_re]
    ring
  have hbound : |((gManu i s).re - (cCoeff i).re) - (bHat f1 i).re * (s - 1)|
      ≤ gh_i * (s - 1) ^ 2 / 2 := by
    rw [hre]
    exact le_trans (Complex.abs_re_le_norm _) (htaylor s hs)
  have hfactor : ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))
      - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      = (((gManu i s).re - (cCoeff i).re) - (bHat f1 i).re * (s - 1))
        * ((2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hW]
  exact mul_le_mul_of_nonneg_right hbound hW

/-- Lemma 3.9 restated with the bracket named. -/
theorem lemma_3_9_bracket (z : ℂ) (hz : Norm.norm z ≤ 2) (s : ℝ)
    (hsmem : s ∈ Set.Ioo (1 : ℝ) 2) (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f s) s) :
    HasDerivAt (fun t : ℝ => G2manu t z) (G2manu s z * cBracket (f s) s z) s := by
  unfold cBracket
  exact lemma_3_9_complex z hz s hsmem f hf

/-- Lemma 3.8's contour representation, unfolded to an explicit circle integral.
Combines gManu_eq_cauchy_coeff with cauchyPowerSeries_apply at w = 1, c = 0.
The s-dependence sits entirely in G2manu s z; the (1/z)^i * z^(-1) factor is
s-free, which is what makes differentiation under the integral clean. -/
theorem gManu_eq_circleIntegral (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (i : ℕ) :
    gManu i s
      = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (circleIntegral (fun z : ℂ => (1 / z) ^ i • z⁻¹ • G2manu s z)
          0 (2 : ℝ)) := by
  have hcoeff : gManu i s
      = (cauchyPowerSeries (fun z : ℂ => G2manu s z) 0 ((2 : NNReal) : ℝ)).coeff i := by
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => G2manu s z)
        (Metric.closedBall (0 : ℂ) ((2 : NNReal) : ℝ)) := by
      apply (G2manu_differentiableOn_wide s hs hk).mono
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      norm_num at hw ⊢
      linarith
    have hR : (0 : NNReal) < 2 := by norm_num
    have hser := hdiff.hasFPowerSeriesOnBall hR
    have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser i
    unfold gManu
    rw [hbridge]
    have hfac : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    field_simp
  rw [hcoeff]
  have h := cauchyPowerSeries_apply (fun z : ℂ => G2manu s z) 0 ((2 : NNReal) : ℝ) i 1
  change ((cauchyPowerSeries (fun z : ℂ => G2manu s z) 0 ((2 : NNReal) : ℝ) i) fun _ => 1) = _
  rw [h]
  norm_num

/-- The contour integrand is continuous in theta.  Discharges the two
measurability obligations and the integrability of F x0 in
hasDerivAt_integral_of_dominated_loc_of_deriv_le: on the circle |z| = 12 / 5 the
factor (1/z)^i * z^(-1) is continuous (z never vanishes) and G2manu s . is
continuous there by G2manu_differentiableOn_wide. -/
theorem contour_integrand_continuous (s : ℝ) (hs : 1 ≤ s) (hk : 0 < kappaFac s) (i : ℕ) :
    Continuous (fun t : ℝ =>
      deriv (circleMap 0 (2 : ℝ)) t
        • ((1 / circleMap 0 (2 : ℝ) t) ^ i
          • (circleMap 0 (2 : ℝ) t)⁻¹ • G2manu s (circleMap 0 (2 : ℝ) t))) := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hne : ∀ t : ℝ, circleMap 0 (2 : ℝ) t ≠ 0 :=
    fun t => circleMap_ne_center (ne_of_gt hR)
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  have hdcm : Continuous (deriv (circleMap 0 (2 : ℝ))) := by
    have : deriv (circleMap 0 (2 : ℝ))
        = fun t => circleMap 0 (2 : ℝ) t * Complex.I := by
      funext t
      exact deriv_circleMap 0 (2 : ℝ) t
    rw [this]
    exact hcm.mul continuous_const
  have hmem : ∀ t : ℝ, circleMap 0 (2 : ℝ) t ∈ Metric.closedBall (0 : ℂ) (2 : ℝ) := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
    simp [circleMap]
  have hG2 : Continuous (fun t : ℝ => G2manu s (circleMap 0 (2 : ℝ) t)) := by
    have hsub : Metric.closedBall (0 : ℂ) (2 : ℝ)
        ⊆ Metric.closedBall (0 : ℂ) ((12 : ℝ)/5) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      linarith
    have hcont := ((G2manu_differentiableOn_wide s hs hk).mono hsub).continuousOn
    exact hcont.comp_continuous hcm hmem
  simp only [smul_eq_mul]
  apply hdcm.mul
  apply Continuous.mul
  · exact (continuous_const.div hcm (fun t => hne t)).pow i
  · exact (hcm.inv₀ (fun t => hne t)).mul hG2

/-- The dominating bound for differentiation under the contour.
On |z| = R = 12 / 5 the non-G2 factors cancel exactly:
  |deriv circleMap| * |(1/z)^i| * |z^(-1)| = R * R^(-i) * (1/R) = R^(-i) <= 1,
so the integrand's s-derivative is bounded by the sup of |d_s G2| alone.

The bound M is a hypothesis: it is
  sup_{t in [1,2], |w| = 12 / 5} ||d_s G2manu t w||,
the analogue of the manuscript's M1 = 2544.  The wide-radius chain now proves
analyticity on |z| <= 29 / 10, so the manuscript's radius 2.9 is available; the
contour here is at 12 / 5, which sits inside it. -/
theorem contour_integrand_deriv_bound (i : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (t : ℝ) (theta : ℝ)
    (hbound : Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t) ≤ M) :
    Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹
            * deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t)))
      ≤ M := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hnorm : Norm.norm (circleMap 0 (2 : ℝ) theta) = 2 := by
    simp [circleMap]
  have hne : circleMap 0 (2 : ℝ) theta ≠ 0 := circleMap_ne_center (ne_of_gt hR)
  have hdcm : Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta) = 2 := by
    rw [deriv_circleMap]
    rw [norm_mul, hnorm, Complex.norm_I]
    ring
  rw [norm_mul, norm_mul, norm_mul, hdcm, norm_pow, norm_div, norm_one, hnorm, norm_inv, hnorm]
  have hpow : ((2 : ℝ))⁻¹ ^ i ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    rw [inv_le_one_iff₀]
    right
    norm_num
  have hMnn : (0 : ℝ) ≤ Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t) :=
    norm_nonneg _
  calc (2 : ℝ) * ((1 / (2 : ℝ)) ^ i
        * (((2 : ℝ))⁻¹
          * Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t)))
      = ((1 / (2 : ℝ)) ^ i)
          * Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t) := by
        field_simp
    _ ≤ 1 * Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t) := by
        apply mul_le_mul_of_nonneg_right _ hMnn
        rw [one_div]
        exact hpow
    _ = Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) t) := one_mul _
    _ ≤ M := hbound

/-- Generalised contour bound: the s-free factors contribute at most 1, so the
integrand is bounded by whatever bounds the varying factor.  The r=1 version
contour_integrand_deriv_bound is this at w = the first derivative; r=2 uses it
at w = the second. -/
theorem contour_integrand_bound_gen (i : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (theta : ℝ) (w : ℂ) (hbound : Norm.norm w ≤ M) :
    Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * w)))
      ≤ M := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hnorm : Norm.norm (circleMap 0 (2 : ℝ) theta) = 2 := by
    simp [circleMap]
  have hne : circleMap 0 (2 : ℝ) theta ≠ 0 := circleMap_ne_center (ne_of_gt hR)
  have hdcm : Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta) = 2 := by
    rw [deriv_circleMap, norm_mul, hnorm, Complex.norm_I]
    ring
  rw [norm_mul, norm_mul, norm_mul, hdcm, norm_pow, norm_div, norm_one, hnorm,
    norm_inv, hnorm]
  have hpow : ((2 : ℝ))⁻¹ ^ i ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    rw [inv_le_one_iff₀]
    right; norm_num
  have hwnn : (0 : ℝ) ≤ Norm.norm w := norm_nonneg _
  calc (2 : ℝ) * ((1 / (2 : ℝ)) ^ i * (((2 : ℝ))⁻¹ * Norm.norm w))
      = ((1 / (2 : ℝ)) ^ i) * Norm.norm w := by field_simp
    _ ≤ 1 * Norm.norm w := by
        apply mul_le_mul_of_nonneg_right _ hwnn
        rw [one_div]; exact hpow
    _ = Norm.norm w := one_mul _
    _ ≤ M := hbound

/-- MANUSCRIPT LEMMA 3.8 at r = 2: the contour integral may be differentiated
twice in s.  Theorem 6.1's Taylor-with-integral-remainder needs exactly this.

M2 bounds the second derivative on the contour, as M bounds the first at r=1:
certified numerically in the manuscript (section 6.1's sup_{s,|z|=2.9}
|G2^(2,0)| <= 19881), so a hypothesis here. -/
theorem lemma_3_8_integral_r2 (i : ℕ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1 : ℝ) 2)
    (D2 : ℝ → ℝ → ℂ)
    (hD2cont : ∀ x : ℝ, Continuous (D2 x))
    (hD2 : ∀ x ∈ Set.Ioo (1 : ℝ) 2, ∀ theta : ℝ,
      HasDerivAt (fun u : ℝ => deriv (fun v : ℝ => G2manu v (circleMap 0 (2 : ℝ) theta)) u)
        (D2 x theta) x)
    (M2 : ℝ) (hM20 : 0 ≤ M2)
    (hM2 : ∀ x ∈ Set.Ioo (1 : ℝ) 2, ∀ theta : ℝ,
      Norm.norm (D2 x theta) ≤ M2)
    (hDcont : ∀ x : ℝ, Continuous (fun theta : ℝ =>
      deriv (fun v : ℝ => G2manu v (circleMap 0 (2 : ℝ) theta)) x)) :
    HasDerivAt (fun t : ℝ => ∫ theta in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹
              * deriv (fun v : ℝ => G2manu v (circleMap 0 (2 : ℝ) theta)) t)))
      (∫ theta in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹ * D2 s theta))) s := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hne : ∀ t : ℝ, circleMap 0 (2 : ℝ) t ≠ 0 :=
    fun t => circleMap_ne_center (ne_of_gt hR)
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  have hdcm : Continuous (deriv (circleMap 0 (2 : ℝ))) := by
    have hd : deriv (circleMap 0 (2 : ℝ)) = fun t => circleMap 0 (2 : ℝ) t * Complex.I := by
      funext t
      exact deriv_circleMap 0 (2 : ℝ) t
    rw [hd]
    exact hcm.mul continuous_const
  have hnhds : Set.Ioo (1 : ℝ) 2 ∈ nhds s := Ioo_mem_nhds hsmem.1 hsmem.2
  have hsfree : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun theta : ℝ =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * g theta))) := by
    intro g hg
    apply hdcm.mul
    apply Continuous.mul
    · exact (continuous_const.div hcm (fun t => hne t)).pow i
    · exact (hcm.inv₀ (fun t => hne t)).mul hg
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℝ) (theta : ℝ) =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹
            * deriv (fun v : ℝ => G2manu v (circleMap 0 (2 : ℝ) theta)) x)))
    (F' := fun (x : ℝ) (theta : ℝ) =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * D2 x theta)))
    (bound := fun _ => M2) (x₀ := s) (s := Set.Ioo (1 : ℝ) 2)
    hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hnhds] with x _
    exact (hsfree _ (hDcont x)).aestronglyMeasurable
  · exact ((hsfree _ (hDcont s)).intervalIntegrable 0 (2 * Real.pi))
  · exact (hsfree _ (hD2cont s)).aestronglyMeasurable
  · filter_upwards with theta _ x hx
    exact contour_integrand_bound_gen i M2 hM20 theta (D2 x theta) (hM2 x hx theta)
  · exact intervalIntegrable_const
  · filter_upwards with theta _ x hx
    exact ((hD2 x hx theta).const_mul _).const_mul _ |>.const_mul _

/-- d/ds G2manu exists at every point of (1,2) on the contour: this is what
makes `deriv (fun u => G2manu u w) x` in Lemma 3.8 denote a real derivative
rather than a junk value. -/
theorem G2manu_differentiableAt_s (w : ℂ) (hw : Norm.norm w ≤ 2) (x : ℝ)
    (hx : x ∈ Set.Ioo (1 : ℝ) 2) (f : ℝ → ℝ)
    (hf : HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x) :
    DifferentiableAt ℝ (fun u : ℝ => G2manu u w) x :=
  (lemma_3_9_complex w hw x hx f hf).differentiableAt

/-- Per-term continuity in theta on the contour |z| = 2.
Both denominators are nonvanishing there: p^s - 1 >= 2 is constant in theta,
and |p^s - z| >= p^s - 2 >= 1 since |z| = 2 and p^s >= 3. -/
theorem clog_term_continuous_theta (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      -(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
          * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2 : ℝ) theta)) := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have hps : (3 : ℝ) ≤ (((p : ℕ):ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p : ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) = 2 := by
    intro theta
    simp [circleMap]
  have hd1 : (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1) ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    have : ((((p : ℕ):ℝ)) ^ s : ℝ) = 1 := by exact_mod_cast hcon
    linarith
  have hd2 : ∀ theta : ℝ,
      (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2 : ℝ) theta) ≠ 0 := by
    intro theta hcon
    rw [sub_eq_zero] at hcon
    have hn := hnorm theta
    rw [← hcon, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < (((p : ℕ):ℝ)) ^ s)] at hn
    linarith
  have hnum : Continuous (fun theta : ℝ =>
      -(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
        * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))) :=
    ((hcm.mul (hcm.sub continuous_const)).mul continuous_const).neg
  have hden : Continuous (fun theta : ℝ =>
      (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2 : ℝ) theta)) :=
    continuous_const.sub hcm
  exact (hnum.div continuous_const (fun _ => hd1)).div hden (fun theta => hd2 theta)

/-- Per-term continuity in theta for the r=2 series, on the contour |z| = 2. -/
theorem clog2_term_continuous_theta (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
          * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
          * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
            + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta) ^ 2)))) := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have hps : (3 : ℝ) ≤ (((p : ℕ):ℝ)) ^ s := by
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      _ ≤ (((p : ℕ):ℝ)) ^ s := Real.rpow_le_rpow (by norm_num) hp3 (by linarith)
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) = 2 := by
    intro theta
    simp [circleMap]
  have hpsC : Norm.norm ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) = (((p : ℕ):ℝ)) ^ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hd1 : (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - 1) ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    have : ((((p : ℕ):ℝ)) ^ s : ℝ) = 1 := by exact_mod_cast hcon
    linarith
  have hd2 : ∀ theta : ℝ,
      (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - circleMap 0 (2 : ℝ) theta) ≠ 0 := by
    intro theta hcon
    rw [sub_eq_zero] at hcon
    have hn := hnorm theta
    rw [← hcon, hpsC] at hn
    linarith
  have hnum : Continuous (fun theta : ℝ =>
      circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
        * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
        * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
          + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)))) :=
    hcm.mul ((((hcm.sub continuous_const).mul continuous_const).mul continuous_const).mul
      ((continuous_const.sub hcm).add continuous_const))
  have hden : Continuous (fun theta : ℝ =>
      (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - 1) ^ 2
        * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - circleMap 0 (2 : ℝ) theta) ^ 2) :=
    continuous_const.mul ((continuous_const.sub hcm).pow 2)
  have hdne : ∀ theta : ℝ,
      (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - 1) ^ 2
        * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)) - circleMap 0 (2 : ℝ) theta) ^ 2 ≠ 0 := by
    intro theta
    exact mul_ne_zero (pow_ne_zero 2 hd1) (pow_ne_zero 2 (hd2 theta))
  have hfun : ∀ theta : ℝ,
      circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
          * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
          * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
            + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
        / (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta) ^ 2)))
      = (circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
          * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
          * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
            + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))))
        / ((((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
          * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta) ^ 2))) := by
    intro theta
    ring
  simp only [hfun]
  exact hnum.div hden hdne

/-- The r=2 series is continuous in theta on the contour.
Mirrors clog_series_continuous_theta; the global bound holds because circleMap
always lands on |z| = 2, where deriv2_clog_term_bound_z applies. -/
theorem clog2_series_continuous_theta (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
            * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
            * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
              + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
          / (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
            * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta) ^ 2))))) := by
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      clog2_term_continuous_theta (p : ℕ) (by omega) s hs)
    deriv2_bound_uniform_summable_five_z
  intro p theta
  exact deriv2_clog_term_bound_z (p : ℕ) (by omega) s hs
    (circleMap 0 (2 : ℝ) theta) (hnorm theta)

/-- C' is continuous in theta on the contour: the kappa-part is constant in
theta apart from the z factor, the p=3 term is clog2_term_continuous_theta at
p = 3, and the tail is clog2_series_continuous_theta. -/
theorem c_bracket_deriv_continuous_theta (s : ℝ) (hs : 1 ≤ s) (fps : ℝ) :
    Continuous (fun theta : ℝ =>
      circleMap 0 (2 : ℝ) theta * (((fps + -((Real.log 2) ^ 2 * (2 : ℝ) ^ s)
            / ((2 : ℝ) ^ s - 1) ^ 2 : ℝ)) : ℂ)
        + ((circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
              * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ) ^ 2 * (((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ)
              * ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
                + ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
            / (((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
              * (((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta) ^ 2))))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (circleMap 0 (2 : ℝ) theta * ((circleMap 0 (2 : ℝ) theta - 1)
                  * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ) ^ 2
                  * (((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
                  * ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta
                    + ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1))
                / (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1) ^ 2
                  * (((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ)
                    - circleMap 0 (2 : ℝ) theta) ^ 2)))))) := by
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  apply Continuous.add (hcm.mul continuous_const)
  apply Continuous.add
  · exact clog2_term_continuous_theta 3 (le_refl 3) s hs
  · exact clog2_series_continuous_theta s hs

/-- The per-prime derivative sum is continuous in theta on the contour.
continuous_tsum needs a GLOBAL bound (all theta), which holds here precisely
because circleMap always lands on |z| = 2, where
deriv_clog_term_bound_uniform applies. -/
theorem clog_series_continuous_theta (s : ℝ) (hs : 1 ≤ s) :
    Continuous (fun theta : ℝ =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
            * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
          / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
            / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2 : ℝ) theta))) := by
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      clog_term_continuous_theta (p : ℕ) (by omega) s hs)
    deriv_bound_uniform_summable_five
  intro p theta
  exact deriv_clog_term_bound_uniform (p : ℕ) (by omega) s hs
    (circleMap 0 (2 : ℝ) theta) (hnorm theta)

/-- C is continuous in theta on the contour: kappa-part, p=3 term, and the
r=1 tail series.  The r=1 analogue of c_bracket_deriv_continuous_theta. -/
theorem c_bracket_continuous_theta (s : ℝ) (hs : 1 ≤ s) (fs : ℝ) :
    Continuous (fun theta : ℝ =>
      circleMap 0 (2 : ℝ) theta * (((fs + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)
        + ((-(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
              * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
            / ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
              / ((((((3 : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta))
          + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
              (-(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
                  * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                / ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - 1)
                  / ((((((p : ℕ):ℝ)) ^ s : ℝ) : ℂ) - circleMap 0 (2 : ℝ) theta)))) := by
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  apply Continuous.add (hcm.mul continuous_const)
  apply Continuous.add
  · exact clog_term_continuous_theta 3 (le_refl 3) s hs
  · exact clog_series_continuous_theta s hs

/-- The second s-derivative of G2manu is continuous in the contour parameter.
Needed for the F' measurability obligation of Lemma 3.8 at r=2.
hasDerivAt_G2manu_second identifies it with G2*(C^2 + C'), and all three
factors are continuous in theta. -/
theorem G2manu_deriv2_continuous_theta (G C Cp : ℝ → ℂ)
    (hG : Continuous G) (hC : Continuous C) (hCp : Continuous Cp) :
    Continuous (fun theta : ℝ => G theta * C theta * C theta + G theta * Cp theta) :=
  ((hG.mul hC).mul hC).add (hG.mul hCp)

/-- The s-derivative of G2manu, as a function of the contour parameter theta,
is continuous.  This is what makes the F' measurability obligation of
Lemma 3.8 discharge: lemma_3_9_complex identifies the deriv with an explicit
expression, and every factor of that expression is continuous in theta. -/
theorem G2manu_deriv_continuous_theta (s : ℝ) (hsmem : s ∈ Set.Ioo (1 : ℝ) 2)
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x) :
    Continuous (fun theta : ℝ =>
      deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) s) := by
  have hs1 : 1 ≤ s := le_of_lt hsmem.1
  have hkap : 0 < kappaFac s := kappaFac_pos s hsmem.1 (cFac_pos s hsmem.1)
  have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  have hval : ∀ theta : ℝ,
      deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) s
        = G2manu s (circleMap 0 (2 : ℝ) theta) *
          (circleMap 0 (2 : ℝ) theta * (((f s + Real.log 2 / ((2 : ℝ) ^ s - 1) : ℝ)) : ℂ)
            + ((-(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
                  * ((Real.log ((3 : ℕ):ℝ) : ℝ) : ℂ))
                / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                  / (((((((3 : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2 : ℝ) theta))
              + ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
                  (-(circleMap 0 (2 : ℝ) theta * (circleMap 0 (2 : ℝ) theta - 1)
                      * ((Real.log ((p : ℕ):ℝ) : ℝ) : ℂ))
                    / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - 1)
                      / (((((((p : ℕ):ℝ)) ^ s : ℝ)) : ℂ) - circleMap 0 (2 : ℝ) theta)))) := by
    intro theta
    exact (lemma_3_9_complex (circleMap 0 (2 : ℝ) theta) (hnorm theta) s hsmem f
      (hf s hsmem)).deriv
  simp only [hval]
  have hG2 : Continuous (fun theta : ℝ => G2manu s (circleMap 0 (2 : ℝ) theta)) := by
    have hsub : Metric.closedBall (0 : ℂ) (2 : ℝ) ⊆ Metric.closedBall (0 : ℂ) ((12 : ℝ)/5) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      linarith
    have hmem : ∀ theta : ℝ, circleMap 0 (2 : ℝ) theta ∈
        Metric.closedBall (0 : ℂ) (2 : ℝ) := by
      intro theta
      rw [Metric.mem_closedBall, dist_zero_right]
      simp [circleMap]
    exact (((G2manu_differentiableOn_wide s hs1 hkap).mono hsub).continuousOn).comp_continuous
      hcm hmem
  apply hG2.mul
  apply Continuous.add
  · exact hcm.mul continuous_const
  · exact (clog_term_continuous_theta 3 (le_refl 3) s hs1).add
      (clog_series_continuous_theta s hs1)

/-- s-free dominator for the correction series at p >= 5, for the
s-continuity argument. -/
theorem correction_bound_uniform_summable_five :
    Summable (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      18 * (((p : ℕ):ℝ)) ^ (-(2 : ℝ))) := by
  have h2 : (-(2 : ℝ)) < -1 := by norm_num
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr h2
  exact (hbase.subtype _).mul_left 18

/-- The correction bound, s-free: 18 p^(-2s) <= 18 p^(-2) for s >= 1. -/
theorem correction_bound_sfree (p : ℕ) (hp : 3 ≤ p) (s : ℝ) (hs : 1 ≤ s)
    (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Norm.norm ((-Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-s) : ℝ) : ℂ)))
        + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-s)) : ℝ) : ℂ))
      ≤ 18 * (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hbase := prime_correction_bound_complex p hp s hs z hz
  have hmono : (((p : ℕ):ℝ)) ^ (-2*s) ≤ (((p : ℕ):ℝ)) ^ (-(2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  linarith

/-- The correction term is continuous in s on {s // 1 <= s}.
The subtype domain is what makes continuous_tsum applicable: continuity fails
for small s (1 - p^(-s) -> 0 there) and the bound 18 p^(-2) needs s >= 1, so
both hold unconditionally only after restricting. -/
theorem correction_continuous_s (p : ℕ) (hp : 3 ≤ p) (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      -Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ))
        + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-(s : ℝ))) : ℝ) : ℂ)) := by
  have hp3 : (3 : ℝ) ≤ (((p : ℕ):ℝ)) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (((p : ℕ):ℝ)) := by linarith
  have hsub : Continuous (fun s : {s : ℝ // 1 ≤ s} => (s : ℝ)) := continuous_subtype_val
  have hrpow : Continuous (fun s : {s : ℝ // 1 ≤ s} => (((p : ℕ):ℝ)) ^ (-(s : ℝ))) :=
    (continuous_const_rpow (ne_of_gt hp0)).comp hsub.neg
  have hlt : ∀ s : {s : ℝ // 1 ≤ s}, (((p : ℕ):ℝ)) ^ (-(s : ℝ)) < 1 :=
    fun s => Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith [s.2])
  have hden : ∀ s : {s : ℝ // 1 ≤ s},
      (0 : ℝ) < 1 - (((p : ℕ):ℝ)) ^ (-(s : ℝ)) := fun s => by linarith [hlt s]
  have hlogr : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      Real.log (1 - (((p : ℕ):ℝ)) ^ (-(s : ℝ)))) :=
    Real.continuousOn_log.comp_continuous (continuous_const.sub hrpow)
      (fun s => ne_of_gt (hden s))
  have hinner : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (1 : ℂ) - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ)) :=
    continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp hrpow))
  have hslit : ∀ s : {s : ℝ // 1 ≤ s},
      (1 : ℂ) - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    fun s => one_sub_mem_slitPlane p hp (s : ℝ) s.2 z hz
  have hlogc : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro s
    have hca : ContinuousAt Complex.log
        (1 - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ)) :=
      (Complex.hasDerivAt_log (hslit s)).continuousAt
    exact ContinuousAt.comp (g := Complex.log)
      (f := fun s : {s : ℝ // 1 ≤ s} =>
        1 - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ))
      hca hinner.continuousAt
  exact hlogc.neg.add (continuous_const.mul (Complex.continuous_ofReal.comp hlogr))

/-- The correction series is continuous in s on {s // 1 <= s}. -/
theorem correction_series_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      ∑' p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        (-Complex.log (1 - z * (((((p : ℕ):ℝ)) ^ (-(s : ℝ)) : ℝ) : ℂ))
          + z * ((Real.log (1 - (((p : ℕ):ℝ)) ^ (-(s : ℝ))) : ℝ) : ℂ))) := by
  apply continuous_tsum
    (fun p : {p : ℕ // p.Prime ∧ 5 ≤ p} =>
      correction_continuous_s (p : ℕ) (by omega) z hz)
    correction_bound_uniform_summable_five
  intro p s
  exact correction_bound_sfree (p : ℕ) (by omega) (s : ℝ) s.2 z hz

/-- G2tailC is continuous in s on {s // 1 <= s}: it is exp of the correction
series (G2tailC_eq_exp_sum), which is continuous by
correction_series_continuous_s. -/
theorem G2tailC_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} => G2tailC (s : ℝ) z) := by
  have hser := correction_series_continuous_s z hz
  have hexp := Complex.continuous_exp.comp hser
  apply hexp.congr
  intro s
  exact (G2tailC_eq_exp_sum (s : ℝ) s.2 z hz).symm

/-- G2C is continuous in s on {s // 1 <= s}: the p = 3 factor times the tail.
The p = 3 factor is continuous because 1 - z*3^(-s) stays in the slit plane
and 1 - 3^(-s) stays positive for s >= 1. -/
theorem G2C_continuous_s (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Continuous (fun s : {s : ℝ // 1 ≤ s} => G2C (s : ℝ) z) := by
  have hrpow : Continuous (fun s : {s : ℝ // 1 ≤ s} => ((3 : ℝ)) ^ (-(s : ℝ))) :=
    (continuous_const_rpow (by norm_num)).comp continuous_subtype_val.neg
  have hlt : ∀ s : {s : ℝ // 1 ≤ s}, ((3 : ℝ)) ^ (-(s : ℝ)) ≤ 1 / 3 := by
    intro s
    have h1 : ((3 : ℝ)) ^ (-(s : ℝ)) ≤ ((3 : ℝ)) ^ (-(1 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith [s.2]
    rw [Real.rpow_neg_one] at h1
    norm_num at h1
    linarith
  have hpos : ∀ s : {s : ℝ // 1 ≤ s}, (0 : ℝ) < 1 - ((3 : ℝ)) ^ (-(s : ℝ)) := by
    intro s
    linarith [hlt s]
  have hlogr : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      Real.log (1 - ((3 : ℝ)) ^ (-(s : ℝ)))) :=
    Real.continuousOn_log.comp_continuous (continuous_const.sub hrpow)
      (fun s => ne_of_gt (hpos s))
  have hcpow : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (((1 - ((3 : ℝ)) ^ (-(s : ℝ)) : ℝ)) : ℂ) ^ z) := by
    have heq : (fun s : {s : ℝ // 1 ≤ s} =>
        (((1 - ((3 : ℝ)) ^ (-(s : ℝ)) : ℝ)) : ℂ) ^ z)
        = fun s : {s : ℝ // 1 ≤ s} =>
          Complex.exp (z * ((Real.log (1 - ((3 : ℝ)) ^ (-(s : ℝ))) : ℝ) : ℂ)) := by
      funext s
      rw [ofReal_cpow_eq_exp (1 - ((3 : ℝ)) ^ (-(s : ℝ))) (hpos s) z]
    rw [heq]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hlogr))
  have hzne : ∀ s : {s : ℝ // 1 ≤ s},
      (1 : ℂ) - z * (((((3 : ℝ)) ^ (-(s : ℝ)) : ℝ)) : ℂ) ≠ 0 := by
    intro s
    have := one_sub_mem_slitPlane 3 (le_refl 3) (s : ℝ) s.2 z hz
    norm_num at this
    exact Complex.slitPlane_ne_zero this
  have hinv : Continuous (fun s : {s : ℝ // 1 ≤ s} =>
      (1 - z * (((((3 : ℝ)) ^ (-(s : ℝ)) : ℝ)) : ℂ))⁻¹) := by
    apply Continuous.inv₀ _ hzne
    exact continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp hrpow))
  unfold G2C
  exact (hinv.mul hcpow).mul (G2tailC_continuous_s z hz)

/-- G2C s z -> G2C 1 z as s -> 1 from above.
G2C_continuous_s gives continuity on the subtype {s // 1 <= s}; the bridge
tendsto_nhdsWithin_iff_subtype converts that to a limit along nhdsWithin 1
(Ici 1), and nhdsWithin 1 (Ioi 1) is finer. -/
theorem G2C_tendsto_at_one (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Filter.Tendsto (fun s : ℝ => G2C s z) (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (G2C 1 z)) := by
  have hmem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (le_refl 1)
  have hcont := G2C_continuous_s z hz
  have hsub : Filter.Tendsto ((Set.Ici (1 : ℝ)).restrict (fun s : ℝ => G2C s z))
      (nhds (⟨(1 : ℝ), hmem⟩ : ↑(Set.Ici (1 : ℝ)))) (nhds (G2C 1 z)) := by
    exact hcont.continuousAt
  have hIci := (tendsto_nhdsWithin_iff_subtype hmem (fun s : ℝ => G2C s z)
    (nhds (G2C 1 z))).mpr hsub
  apply hIci.mono_left
  apply nhdsWithin_mono
  intro x hx
  exact le_of_lt (Set.mem_Ioi.mp hx)

/-- kappa(s)^z -> (1 / 2)^z as s -> 1 from above. -/
theorem kappa_cpow_tendsto (z : ℂ) :
    Filter.Tendsto (fun s : ℝ => ((kappaFac s : ℝ) : ℂ) ^ z)
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds ((((1 / 2 : ℝ)) : ℂ) ^ z)) := by
  have hk := kappaFac_tendsto_half
  have heq : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) →
      ((kappaFac s : ℝ) : ℂ) ^ z = Complex.exp (z * ((Real.log (kappaFac s) : ℝ) : ℂ)) := by
    intro s hs
    exact ofReal_cpow_eq_exp (kappaFac s) (kappaFac_pos s hs (cFac_pos s hs)) z
  have hlog : Filter.Tendsto (fun s : ℝ => Real.log (kappaFac s))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (Real.log (1 / 2 : ℝ))) := by
    apply (Real.continuousAt_log (by norm_num)).tendsto.comp hk
  have hcomp : Filter.Tendsto (fun s : ℝ => Complex.exp (z * ((Real.log (kappaFac s) : ℝ) : ℂ)))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (Complex.exp (z * ((Real.log (1 / 2 : ℝ) : ℝ) : ℂ)))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    apply Filter.Tendsto.const_mul
    exact (Complex.continuous_ofReal.continuousAt).tendsto.comp hlog
  have hval : Complex.exp (z * ((Real.log (1 / 2 : ℝ) : ℝ) : ℂ)) = (((1 / 2 : ℝ)) : ℂ) ^ z :=
    (ofReal_cpow_eq_exp (1 / 2 : ℝ) (by norm_num) z).symm
  rw [← hval]
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (heq s hs).symm

/-- G2manu s z -> G2at1 z as s -> 1 from above.
Product of kappa_cpow_tendsto and G2C_tendsto_at_one, since
G2manu s z = kappa(s)^z * G2C s z and G2at1 z = (1 / 2)^z * G2C 1 z. -/
theorem G2manu_tendsto_G2at1 (z : ℂ) (hz : Norm.norm z ≤ 2) :
    Filter.Tendsto (fun s : ℝ => G2manu s z) (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (G2at1 z)) := by
  have hprod := (kappa_cpow_tendsto z).mul (G2C_tendsto_at_one z hz)
  have hval : G2at1 z = (((1 / 2 : ℝ)) : ℂ) ^ z * G2C 1 z := rfl
  rw [hval]
  apply hprod.congr
  intro s
  unfold G2manu
  ring

/-- The s-derivative of G2manu converges pointwise on the contour as s -> 1+:
G2manu s z * cBracket (f s) s z -> G2at1 z * cBracket f1 1 z = G2deriv1 f1 z.
The f-argument converges because f is continuous at 1 (hypothesis hfc). -/
theorem G2deriv_tendsto_at_one (z : ℂ) (hz : Norm.norm z ≤ 2)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds f1))
    (hbr : Filter.Tendsto (fun s : ℝ => cBracket (f s) s z)
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (cBracket f1 1 z))) :
    Filter.Tendsto (fun s : ℝ => G2manu s z * cBracket (f s) s z)
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (G2deriv1 f1 z)) := by
  unfold G2deriv1
  exact (G2manu_tendsto_G2at1 z hz).mul hbr

/-- The derivative integrand converges pointwise in theta as s -> 1+. -/
theorem deriv_integrand_tendsto (i : ℕ) (theta : ℝ)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds f1)) :
    Filter.Tendsto (fun s : ℝ =>
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹
              * (G2manu s (circleMap 0 (2 : ℝ) theta)
                * cBracket (f s) s (circleMap 0 (2 : ℝ) theta)))))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹
            * G2deriv1 f1 (circleMap 0 (2 : ℝ) theta))))) := by
  have hnorm : Norm.norm (circleMap 0 (2 : ℝ) theta) ≤ 2 := by
    simp [circleMap]
  have hbr := cBracket_tendsto_two_arg (circleMap 0 (2 : ℝ) theta) hnorm f f1 hfc
  have hG2 := G2deriv_tendsto_at_one (circleMap 0 (2 : ℝ) theta) hnorm f f1 hfc hbr
  exact (hG2.const_mul _).const_mul _ |>.const_mul _

/-- The derivative contour integral converges as s -> 1+, by dominated
convergence.  M is the same first-derivative bound lemma_3_8_integral_r1
carries -- no new hypothesis. -/
theorem deriv_contour_integral_tendsto (i : ℕ)
    (f : ℝ → ℝ) (f1 : ℝ)
    (hfc : Filter.Tendsto f (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds f1))
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta)
        * cBracket (f s) s (circleMap 0 (2 : ℝ) theta)) ≤ M)
    (hcont : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) → Continuous (fun theta : ℝ =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹
            * (G2manu s (circleMap 0 (2 : ℝ) theta)
              * cBracket (f s) s (circleMap 0 (2 : ℝ) theta)))))) :
    Filter.Tendsto (fun s : ℝ =>
        ∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap 0 (2 : ℝ)) theta
            * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
              * ((circleMap 0 (2 : ℝ) theta)⁻¹
                * (G2manu s (circleMap 0 (2 : ℝ) theta)
                  * cBracket (f s) s (circleMap 0 (2 : ℝ) theta)))))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹
              * G2deriv1 f1 (circleMap 0 (2 : ℝ) theta))))) := by
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hcont s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with theta
    exact contour_integrand_bound_gen i M hM0 theta
      (G2manu s (circleMap 0 (2 : ℝ) theta)
        * cBracket (f s) s (circleMap 0 (2 : ℝ) theta)) (hM s hs theta)
  · exact MeasureTheory.integrable_const M
  · filter_upwards with theta
    exact deriv_integrand_tendsto i theta f f1 hfc

/-- The contour integrand converges pointwise in theta as s -> 1+.
The s-free factors are constant in s; only G2manu moves, and
G2manu_tendsto_G2at1 gives its limit at each point of the contour. -/
theorem contour_integrand_tendsto (i : ℕ) (theta : ℝ) :
    Filter.Tendsto (fun s : ℝ =>
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2manu s (circleMap 0 (2 : ℝ) theta))))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2at1 (circleMap 0 (2 : ℝ) theta))))) := by
  have hnorm : Norm.norm (circleMap 0 (2 : ℝ) theta) ≤ 2 := by
    simp [circleMap]
  have hG2 := G2manu_tendsto_G2at1 (circleMap 0 (2 : ℝ) theta) hnorm
  exact (hG2.const_mul _).const_mul _ |>.const_mul _

/-- The contour integral converges as s -> 1+, by dominated convergence.
M0 is a hypothesis: sup over s in (1,2), |z| = 2 of ||G2manu s z||, the
analogue of the manuscript's M = 326 (Lemma 3.7) at our radius.  Certified
numerically there, so assumed here, as with M1. -/
theorem contour_integral_tendsto (i : ℕ) (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    Filter.Tendsto (fun s : ℝ =>
        ∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap 0 (2 : ℝ)) theta
            * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
              * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2manu s (circleMap 0 (2 : ℝ) theta))))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2at1 (circleMap 0 (2 : ℝ) theta))))) := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hne : ∀ t : ℝ, circleMap 0 (2 : ℝ) t ≠ 0 :=
    fun t => circleMap_ne_center (ne_of_gt hR)
  have hdcm : ∀ theta : ℝ, Norm.norm (deriv (circleMap 0 (2 : ℝ)) theta) = 2 := by
    intro theta
    rw [deriv_circleMap, norm_mul, Complex.norm_I]
    simp [circleMap]
  have hnorm : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) = 2 := by
    intro theta
    simp [circleMap]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M0)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hkap : 0 < kappaFac s := kappaFac_pos s hs (cFac_pos s hs)
    exact (contour_integrand_continuous s (le_of_lt hs) hkap i).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with theta
    rw [norm_mul, norm_mul, norm_mul, hdcm, norm_pow, norm_div, norm_one, hnorm,
      norm_inv, hnorm]
    have hb := hM0 s hs theta
    have hp2 : ((2 : ℝ))⁻¹ ^ i ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      rw [inv_le_one_iff₀]
      right; norm_num
    calc (2 : ℝ) * ((1 / (2 : ℝ)) ^ i * ((2 : ℝ)⁻¹ * Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta))))
        = ((1 / (2 : ℝ)) ^ i) * Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta)) := by
          field_simp
      _ ≤ 1 * Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta)) := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [one_div]; exact hp2
      _ = Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta)) := one_mul _
      _ ≤ M0 := hb
  · exact MeasureTheory.integrable_const M0
  · filter_upwards with theta
    exact contour_integrand_tendsto i theta

/-- cCoeff as a contour integral at radius 2, the G2at1 analogue of
gManu_eq_circleIntegral.  G2at1 is differentiable on closedBall 0 (12 / 5)
(G2at1_differentiableOn_wide), which contains closedBall 0 2. -/
theorem cCoeff_eq_circleIntegral (i : ℕ) :
    cCoeff i
      = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (circleIntegral (fun z : ℂ => (1 / z) ^ i • z⁻¹ • G2at1 z)
          0 (2 : ℝ)) := by
  have hdiff : DifferentiableOn ℂ G2at1 (Metric.closedBall (0 : ℂ) ((2 : NNReal) : ℝ)) := by
    apply G2at1_differentiableOn_wide.mono
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    norm_num at hw ⊢
    linarith
  have hR : (0 : NNReal) < 2 := by norm_num
  have hser := hdiff.hasFPowerSeriesOnBall hR
  have hbridge := iteratedDeriv_eq_factorial_smul_coeff' hser i
  have hcoeff : cCoeff i
      = (cauchyPowerSeries G2at1 0 ((2 : NNReal) : ℝ)).coeff i := by
    unfold cCoeff
    rw [hbridge]
    have hfac : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    field_simp
  rw [hcoeff]
  have h := cauchyPowerSeries_apply G2at1 0 ((2 : NNReal) : ℝ) i 1
  change ((cauchyPowerSeries G2at1 0 ((2 : NNReal) : ℝ) i) fun _ => 1) = _
  rw [h]
  norm_num

/-- THE s -> 1 LIMIT: g_i(s) -> c_i as s -> 1 from above.
This is the fact deferred since section 2 and needed by section 3.5's mean
value step.  It cannot be stated as g_i(1) = c_i: kappaFac 1 = 0 by the
tprod junk-value convention (cFac diverges at s = 1), so G2manu is not
defined there.  cCoeff is defined instead through G2at1's explicit product. -/
theorem gManu_tendsto_cCoeff (i : ℕ) (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu s (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    Filter.Tendsto (fun s : ℝ => gManu i s) (nhdsWithin 1 (Set.Ioi (1 : ℝ)))
      (nhds (cCoeff i)) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hint := contour_integral_tendsto i M0 hM00 hM0
  have hci : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) →
      gManu i s = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap 0 (2 : ℝ)) theta
            * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
              * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2manu s (circleMap 0 (2 : ℝ) theta)))) := by
    intro s hs
    have hkap : 0 < kappaFac s := kappaFac_pos s hs (cFac_pos s hs)
    rw [gManu_eq_circleIntegral s (le_of_lt hs) hkap i]
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le hpi]
    simp only [smul_eq_mul]
  have hcc : cCoeff i = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
      • (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2at1 (circleMap 0 (2 : ℝ) theta)))) := by
    rw [cCoeff_eq_circleIntegral i]
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le hpi]
    simp only [smul_eq_mul]
  rw [hcc]
  apply (hint.const_smul _).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hci s hs).symm

/-- Interior form of the mean value bound: for 1 < t, s < 2,
||g_i(s) - g_i(t)|| <= beta * |s - t|, given a derivative bound beta on (1,2).
The endpoint version follows by letting t -> 1+ and using gManu_tendsto_cCoeff. -/
theorem gManu_lipschitz_interior (i : ℕ) (beta : ℝ)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (t s : ℝ) (ht : t ∈ Set.Ioo (1 : ℝ) 2) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    Norm.norm (gManu i s - gManu i t) ≤ beta * Norm.norm (s - t) := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun x : ℝ => deriv (fun u : ℝ => gManu i u) x)
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_Ioo 1 2) ht hs

/-- MANUSCRIPT section 3.5, the mean value step:
||g_i(s) - c_i|| <= (s-1) * beta_i for s in (1,2).
The endpoint is reached by a limit rather than by evaluation: gManu i 1 is a
junk value (kappaFac 1 = 0), so c_i enters through gManu_tendsto_cCoeff. -/
theorem gManu_sub_cCoeff_bound (i : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0)
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    Norm.norm (gManu i s - cCoeff i) ≤ beta * (s - 1) := by
  have hlim := gManu_tendsto_cCoeff i M0 hM00 hM0
  have hsublim : Filter.Tendsto (fun t : ℝ => Norm.norm (gManu i s - gManu i t))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (Norm.norm (gManu i s - cCoeff i))) := by
    apply Filter.Tendsto.norm
    exact tendsto_const_nhds.sub hlim
  have hmem : Set.Ioo (1 : ℝ) s ∈ nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)) :=
    Ioo_mem_nhdsGT hs.1
  have hbnd : ∀ᶠ t in nhdsWithin 1 (Set.Ioi (1 : ℝ)),
      Norm.norm (gManu i s - gManu i t) ≤ beta * (s - 1) := by
    filter_upwards [hmem] with t ht
    have ht2 : t ∈ Set.Ioo (1 : ℝ) 2 :=
      Set.mem_Ioo.mpr (⟨ ht.1, lt_trans ht.2 hs.2 ⟩)
    have hlip := gManu_lipschitz_interior i beta hderiv hbound t s ht2 hs
    have hst : Norm.norm (s - t) ≤ s - 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
      linarith [ht.1]
    calc Norm.norm (gManu i s - gManu i t) ≤ beta * Norm.norm (s - t) := hlip
      _ ≤ beta * (s - 1) := by
          apply mul_le_mul_of_nonneg_left hst hbeta0
  exact le_of_tendsto hsublim hbnd

/-- First-order Taylor step: if D is differentiable on (1,2) with ||D'|| <= g
there, and D(s) -> b as s -> 1+, then ||D(s) - b|| <= g (s-1).
Abstracted from gManu_sub_cCoeff_bound: the same interior-Lipschitz plus
endpoint-limit argument, stated for an arbitrary D so it serves both
D = g_i (giving the beta bound) and D = d_s g_i (giving the gammahat bound). -/
theorem deriv_sub_limit_bound (D : ℝ → ℂ) (b : ℂ) (g : ℝ) (hg0 : 0 ≤ g)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2, HasDerivAt D (deriv D x) x)
    (hbound : ∀ x ∈ Set.Ioo (1 : ℝ) 2, Norm.norm (deriv D x) ≤ g)
    (hlim : Filter.Tendsto D (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds b))
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    Norm.norm (D s - b) ≤ g * (s - 1) := by
  have hsublim : Filter.Tendsto (fun t : ℝ => Norm.norm (D s - D t))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (Norm.norm (D s - b))) := by
    apply Filter.Tendsto.norm
    exact tendsto_const_nhds.sub hlim
  have hmem : Set.Ioo (1 : ℝ) s ∈ nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)) :=
    Ioo_mem_nhdsGT hs.1
  have hbnd : ∀ᶠ t in nhdsWithin 1 (Set.Ioi (1 : ℝ)),
      Norm.norm (D s - D t) ≤ g * (s - 1) := by
    filter_upwards [hmem] with t ht
    have ht2 : t ∈ Set.Ioo (1 : ℝ) 2 :=
      Set.mem_Ioo.mpr (⟨ ht.1, lt_trans ht.2 hs.2 ⟩)
    have hlip : Norm.norm (D s - D t) ≤ g * Norm.norm (s - t) := by
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f' := fun x : ℝ => deriv D x)
        (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_Ioo 1 2) ht2 hs
    have hst : Norm.norm (s - t) ≤ s - 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
      linarith [ht.1]
    calc Norm.norm (D s - D t) ≤ g * Norm.norm (s - t) := hlip
      _ ≤ g * (s - 1) := mul_le_mul_of_nonneg_left hst hg0
  exact le_of_tendsto hsublim hbnd

/-- Second-order Taylor bound: if phi is differentiable on (1,2) with
||phi'(x)|| <= g (x-1) there, and phi(t) -> 0 as t -> 1+, then
||phi(s)|| <= g (s-1)^2 / 2.

This is the step that turns the first-order bound of deriv_sub_limit_bound
into the quadratic remainder of Theorem 6.1.  Proved by the same
interior-plus-limit route, with the interior step bounding
||phi(s) - phi(t)|| by the integral of the linear bound. -/
theorem quadratic_remainder_bound (phi : ℝ → ℂ) (g : ℝ) (hg0 : 0 ≤ g)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2, HasDerivAt phi (deriv phi x) x)
    (hbound : ∀ x ∈ Set.Ioo (1 : ℝ) 2, Norm.norm (deriv phi x) ≤ g * (x - 1))
    (hlim : Filter.Tendsto phi (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds 0))
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    Norm.norm (phi s) ≤ g * (s - 1) ^ 2 / 2 := by
  have hlin : ∀ t : ℝ, t ∈ Set.Ioo (1 : ℝ) s →
      Norm.norm (phi s - phi t) ≤ g * ((s - 1) ^ 2 - (t - 1) ^ 2) / 2 := by
    intro t ht
    have hts : t ≤ s := le_of_lt ht.2
    have hsub : Set.uIcc t s ⊆ Set.Ioo (1 : ℝ) 2 := by
      rw [Set.uIcc_of_le hts]
      intro x hx
      exact Set.mem_Ioo.mpr ⟨ lt_of_lt_of_le ht.1 hx.1, lt_of_le_of_lt hx.2 hs.2 ⟩
    have hgcont : Continuous (fun x : ℝ => g * (x - 1)) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    have hint : IntervalIntegrable (fun x : ℝ => deriv phi x) MeasureTheory.volume t s := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hts]
      have hgi : MeasureTheory.IntegrableOn (fun x : ℝ => g * (x - 1)) (Set.Ioc t s) :=
        (hgcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
      apply MeasureTheory.Integrable.mono hgi
        (measurable_deriv phi).aestronglyMeasurable.restrict
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
      have hyIoo : y ∈ Set.Ioo (1 : ℝ) 2 := by
        apply hsub
        rw [Set.uIcc_of_le hts]
        exact ⟨ le_of_lt hy.1, hy.2 ⟩
      have hnn : (0 : ℝ) ≤ g * (y - 1) := by
        apply mul_nonneg hg0
        linarith [hyIoo.1]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hbound y hyIoo
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (hsub hx)) hint
    rw [← hftc]
    have hbnd : Norm.norm (∫ y in t..s, deriv phi y)
        ≤ ∫ y in t..s, g * (y - 1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hts
      · filter_upwards with y hy
        exact hbound y (hsub (by rw [Set.uIcc_of_le hts]; exact ⟨ le_of_lt hy.1, hy.2 ⟩))
      · exact hgcont.intervalIntegrable t s
    have heval : (∫ y in t..s, g * (y - 1))
        = g * ((s - 1) ^ 2 - (t - 1) ^ 2) / 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hanti : ∀ y ∈ Set.uIcc t s,
          HasDerivAt (fun x : ℝ => (x - 1) ^ 2 / 2) (y - 1) y := by
        intro y _
        have hb : HasDerivAt (fun x : ℝ => x - 1) 1 y := (hasDerivAt_id y).sub_const 1
        have hp : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (y - 1) ^ 1 * 1) y := hb.pow 2
        have hq := hp.div_const 2
        have hval : y - 1 = 2 * (y - 1) ^ 1 * 1 / 2 := by ring
        rw [hval]
        exact hq
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hanti
        ((continuous_id.sub continuous_const).intervalIntegrable t s)]
      ring
    rw [heval] at hbnd
    exact hbnd
  have hsublim : Filter.Tendsto (fun t : ℝ => Norm.norm (phi s - phi t))
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds (Norm.norm (phi s - 0))) := by
    apply Filter.Tendsto.norm
    exact tendsto_const_nhds.sub hlim
  simp only [sub_zero] at hsublim
  apply le_of_tendsto hsublim
  filter_upwards [Ioo_mem_nhdsGT hs.1] with t ht
  have h := hlin t ht
  nlinarith [h, sq_nonneg (t - 1), hg0]

/-- MANUSCRIPT Theorem 6.1's Taylor step, abstracted:
if D is twice differentiable on (1,2) with ||D''|| <= g, and D -> c, D' -> b
as s -> 1+, then ||D s - c - (s-1) b|| <= g (s-1)^2 / 2.

Applied with D = g_i, c = c_i, b = bHat_i, g = gammahat_i this is exactly
g_i(s) = c_i + (s-1) bHat_i + R_i(s) with |R_i(s)| <= (s-1)^2 gammahat_i / 2. -/
theorem taylor_second_bound (D : ℝ → ℂ) (c b : ℂ) (g : ℝ) (hg0 : 0 ≤ g)
    (hD : ∀ x ∈ Set.Ioo (1 : ℝ) 2, HasDerivAt D (deriv D x) x)
    (hD2 : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun u : ℝ => deriv D u) (deriv (fun u : ℝ => deriv D u) x) x)
    (hbound2 : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun u : ℝ => deriv D u) x) ≤ g)
    (hlimD : Filter.Tendsto D (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds c))
    (hlimD1 : Filter.Tendsto (fun u : ℝ => deriv D u)
      (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds b))
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    Norm.norm (D s - c - (((s - 1 : ℝ)) : ℂ) * b) ≤ g * (s - 1) ^ 2 / 2 := by
  set phi : ℝ → ℂ := fun x : ℝ => D x - c - (((x - 1 : ℝ)) : ℂ) * b with hphi
  have hphider : ∀ x ∈ Set.Ioo (1 : ℝ) 2, HasDerivAt phi (deriv D x - b) x := by
    intro x hx
    have h1 := hD x hx
    have h2 : HasDerivAt (fun u : ℝ => (((u - 1 : ℝ)) : ℂ) * b) b x := by
      have hb : HasDerivAt (fun u : ℝ => (((u - 1 : ℝ)) : ℂ)) 1 x := by
        have := ((hasDerivAt_id x).sub_const 1).ofReal_comp
        simpa using this
      simpa using hb.mul_const b
    exact (h1.sub_const c).sub h2
  have hderivEq : ∀ x ∈ Set.Ioo (1 : ℝ) 2, deriv phi x = deriv D x - b :=
    fun x hx => (hphider x hx).deriv
  have hlin : ∀ x ∈ Set.Ioo (1 : ℝ) 2, Norm.norm (deriv phi x) ≤ g * (x - 1) := by
    intro x hx
    rw [hderivEq x hx]
    exact deriv_sub_limit_bound (fun u : ℝ => deriv D u) b g hg0 hD2 hbound2 hlimD1 x hx
  have hlim0 : Filter.Tendsto phi (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => (((x - 1 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)
    have hx : Filter.Tendsto (fun x : ℝ => (((x - 1 : ℝ)) : ℂ))
        (nhdsWithin 1 (Set.Ioi (1 : ℝ))) (nhds 0) := by
      have h : Filter.Tendsto (fun x : ℝ => (((x - 1 : ℝ)) : ℂ))
          (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds ((((1 : ℝ) - 1 : ℝ)) : ℂ)) :=
        (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
      simpa using h
    have hsb := hx.mul_const b
    simp only [zero_mul] at hsb
    have hcomb := (hlimD.sub (tendsto_const_nhds (x := c))).sub hsb
    simp only [sub_self] at hcomb
    rw [hphi]
    exact hcomb
  exact quadratic_remainder_bound phi g hg0
    (fun x hx => by rw [hderivEq x hx]; exact hphider x hx) hlin hlim0 s hs

/-- gManu i is bounded on (1,2) by ||c_i|| + beta_i, from the mean value step.
This is what makes the Ik-side integrands dominated, hence integrable, hence
the sum-integral interchange of Dk_eq_triple_sum available. -/
theorem gManu_bounded (i : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0)
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    Norm.norm (gManu i s) ≤ Norm.norm (cCoeff i) + beta := by
  have hmv := gManu_sub_cCoeff_bound i beta hbeta0 hderiv hbound M0 hM00 hM0 s hs
  have hs1 : s - 1 ≤ 1 := by linarith [hs.2]
  have hbs : beta * (s - 1) ≤ beta := by
    calc beta * (s - 1) ≤ beta * 1 := by
          apply mul_le_mul_of_nonneg_left hs1 hbeta0
      _ = beta := mul_one beta
  calc Norm.norm (gManu i s)
      = Norm.norm ((gManu i s - cCoeff i) + cCoeff i) := by ring_nf
    _ ≤ Norm.norm (gManu i s - cCoeff i) + Norm.norm (cCoeff i) := norm_add_le _ _
    _ ≤ beta * (s - 1) + Norm.norm (cCoeff i) := by linarith [hmv]
    _ ≤ beta + Norm.norm (cCoeff i) := by linarith [hbs]
    _ = Norm.norm (cCoeff i) + beta := by ring

/-- gManu i is continuous on (1,2), from differentiability there. -/
theorem gManu_continuousOn (i : ℕ)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x) :
    ContinuousOn (fun t : ℝ => gManu i t) (Set.Ioo (1 : ℝ) 2) :=
  fun x hx => ((hderiv x hx).continuousAt).continuousWithinAt

/-- The Ik-side integrand is integrable on (1,2], by domination against
integrable_Sm_integrand scaled by the gManu bound.  This is what unblocks the
sum-integral interchange in Dk_eq_triple_sum. -/
theorem integrable_Ik_term (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (gManu i s).re * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (Set.Ioc (1 : ℝ) 2) := by
  have hdomIoc := (integrable_Sm_integrand l j).const_mul (Norm.norm (cCoeff i) + beta)
  have hdomIoo : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Norm.norm (cCoeff i) + beta) *
        ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (2 : ℝ) ^ (-(j : ℝ) * s)))
      (Set.Ioo (1 : ℝ) 2) :=
    MeasureTheory.IntegrableOn.mono_set hdomIoc Set.Ioo_subset_Ioc_self
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (gManu i s).re * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) 2)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact Complex.continuous_re.comp_continuousOn (gManu_continuousOn i hderiv)
      · apply Continuous.continuousOn
        exact (continuous_const_rpow (by norm_num)).comp (continuous_const.mul continuous_id)
    · apply ContinuousOn.div_const
      apply ContinuousOn.pow
      apply ContinuousOn.neg
      apply Real.continuousOn_log.comp (continuousOn_id.sub continuousOn_const)
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, id_eq]
      intro hcon
      simp only [Pi.sub_apply, id_eq] at hcon
      have hx1 : x = 1 := by linarith
      exact absurd hx1 (ne_of_gt hx.1)
  have hIoo : MeasureTheory.IntegrableOn
      (fun s : ℝ => (gManu i s).re * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      (Set.Ioo (1 : ℝ) 2) := by
    apply MeasureTheory.Integrable.mono hdomIoo hmeas
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
    have hb := gManu_bounded i beta hbeta0 hderiv hbound M0 hM00 hM0 s hs
    have hre : |(gManu i s).re| ≤ Norm.norm (gManu i s) := Complex.abs_re_le_norm _
    have hlog : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
      apply div_nonneg _ (by positivity)
      apply pow_nonneg
      have : s - 1 ≤ 1 := by linarith [hs.2]
      have hpos : (0 : ℝ) < s - 1 := by linarith [hs.1]
      simp only [neg_nonneg]
      exact Real.log_nonpos (le_of_lt hpos) this
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
    have hcb : (0 : ℝ) ≤ Norm.norm (cCoeff i) + beta := by positivity
    have hkey : |(gManu i s).re| ≤ Norm.norm (cCoeff i) + beta := le_trans hre hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hrhsnn : (0 : ℝ) ≤ (Norm.norm (cCoeff i) + beta)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (2 : ℝ) ^ (-(j : ℝ) * s)) := by
      apply mul_nonneg hcb
      positivity
    have hlhsnn : (0 : ℝ) ≤ |(gManu i s).re| * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)) := by positivity
    rw [abs_of_nonneg hrhsnn, abs_mul, abs_mul, abs_of_pos h2, abs_of_nonneg hlog]
    have hAB : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)) := by positivity
    calc |(gManu i s).re| * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))
        = |(gManu i s).re| * ((2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) := by ring
      _ ≤ (Norm.norm (cCoeff i) + beta) * ((2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) :=
          mul_le_mul_of_nonneg_right hkey hAB
      _ = (Norm.norm (cCoeff i) + beta) * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)
            * (2 : ℝ) ^ (-(j : ℝ) * s)) := by ring
  exact hIoo.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm

/-- Real-valued conv_flatten: the triangular double sum as a sigma sum. -/
theorem conv_flatten_real (k : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k - p + 1), g p q
      = ∑ x ∈ (Finset.range (k + 1)).sigma (fun p => Finset.range (k - p + 1)),
          g x.1 x.2 := by
  rw [Finset.sum_sigma]

/-- Swapping the two indices of a triangular double sum.
Fk_expansion_manu sums (2-index outer, g-index inner); Ikfrozen sums the other
way round.  This reconciles them. -/
theorem triangular_sum_comm (k : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k - p + 1), g p q
      = ∑ q ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (k - q + 1), g p q := by
  rw [conv_flatten_real, conv_flatten_real]
  apply Finset.sum_nbij'
    (i := fun x : Sigma (fun _ : ℕ => ℕ) => Sigma.mk x.2 x.1)
    (j := fun y : Sigma (fun _ : ℕ => ℕ) => Sigma.mk y.2 y.1)
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · intro x _
    rfl
  · intro y _
    rfl
  · intro x _
    rfl

/-- The Ik side as a triangular double sum of integrals. -/
theorem Ik_eq_double_sum (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    Ik k = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
      (∫ s in Set.Ioc (1 : ℝ) 2,
        (gManu i s).re * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
  unfold Ik
  have hpt : ∀ s ∈ Set.Ioc (1 : ℝ) 2, Fk k s
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (gManu i s).re * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))) := by
    intro s hs
    rw [Fk_expansion_manu k hk s hs.1 hs.2]
    rw [triangular_sum_comm k (fun p q =>
      (gManu q s).re * (2 : ℝ) ^ (-(p : ℝ) * s)
        * ((-Real.log (s - 1)) ^ (k - p - q) / (Nat.factorial (k - p - q))))]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show k - j - i = k - i - j by omega]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbound i)
      M0 hM00 hM0
  · intro i _
    apply MeasureTheory.integrable_finsetSum
    intro j _
    exact integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbound i)
      M0 hM00 hM0

/-- The frozen side as a triangular double sum of integrals.
Simpler than the Ik side: cCoeff is constant in s, and integrability is
integrable_Sm_integrand. -/
theorem Ikfrozen_re_eq_double_sum (k : ℕ) :
    (Ikfrozen k).re
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (∫ s in Set.Ioc (1 : ℝ) 2,
          (cCoeff i).re * (2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
  rw [Ikfrozen_re_eq]
  apply Finset.sum_congr rfl
  intro i _
  unfold Sm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro s _
  ring

/-- MANUSCRIPT (4): D_k as a triple sum.
D_k = sum_{i+j+l=k} int_1^2 (g_i(s) - c_i) 2^(-js) (-log(s-1))^l/l! ds.
Both Ik and Ikfrozen become triangular double sums over the same region; the
index orders differ (triangular_sum_comm reconciles them) and the finite sums
pass through the integral (integrable_Ik_term and integrable_Sm_integrand). -/
theorem Dk_eq_triple_sum (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbound : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    Dk k = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
      (∫ s in Set.Ioc (1 : ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
  unfold Dk
  rw [Ik_eq_double_sum k hk beta hbeta0 hderiv hbound M0 hM00 hM0,
    Ikfrozen_re_eq_double_sum k]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← MeasureTheory.integral_sub]
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro s _
    ring
  · exact integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbound i)
      M0 hM00 hM0
  · have h := (integrable_Sm_integrand (k - i - j) j).const_mul ((cCoeff i).re)
    apply MeasureTheory.IntegrableOn.congr_fun h _ measurableSet_Ioc
    intro s _
    ring

/-- Pointwise bound for (10)'s integrand on (1,2).
|(g_i(s) - c_i) 2^(-js) L_l(s)| <= beta * 2^(-j) * (L_l(s) * (s-1)),
from the mean value step, 2^(-js) <= 2^(-j) for s >= 1, and L_l >= 0. -/
theorem Dk_integrand_ptwise (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0)
    (s : ℝ) (hs : s ∈ Set.Ioo (1 : ℝ) 2) :
    |((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))|
      ≤ beta * (2 : ℝ) ^ (-(j : ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
  have hmv := gManu_sub_cCoeff_bound i beta hbeta0 hderiv hbnd M0 hM00 hM0 s hs
  have hL : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) := by
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
  have hB : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  have hBle : (2 : ℝ) ^ (-(j : ℝ) * s) ≤ (2 : ℝ) ^ (-(j : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    nlinarith [hs.1]
  have hA : |(gManu i s).re - (cCoeff i).re| ≤ beta * (s - 1) := by
    have hre : |(gManu i s).re - (cCoeff i).re|
        = |(gManu i s - cCoeff i).re| := by
      rw [Complex.sub_re]
    rw [hre]
    exact le_trans (Complex.abs_re_le_norm _) hmv
  have hs1 : (0 : ℝ) ≤ s - 1 := by linarith [hs.1]
  rw [abs_mul, abs_mul, abs_of_pos hB, abs_of_nonneg hL]
  calc |(gManu i s).re - (cCoeff i).re| * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))
      ≤ (beta * (s - 1)) * (2 : ℝ) ^ (-(j : ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)) := by
        apply mul_le_mul_of_nonneg_right _ hL
        apply mul_le_mul hA hBle (le_of_lt hB) (by positivity)
    _ = beta * (2 : ℝ) ^ (-(j : ℝ))
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by ring

/-- MANUSCRIPT section 3.5: the exact evaluation
  int_1^2 (-log(s-1))^l / l! * (s-1) ds = 2^(-l-1).
Substitution s = 1 + e^(-t) (integral_Ioc_subst) turns it into
int_0^inf u^l/l! * e^(-2u) du, evaluated by integral_pow_exp_neg_two_mul.
Verified numerically at l = 0,1,2,5. -/
theorem integral_log_pow_sub_one (l : ℕ) :
    (∫ s in Set.Ioc (1 : ℝ) 2,
      (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1))
      = 1 / (2 : ℝ) ^ (l + 1) := by
  rw [integral_Ioc_subst (fun s : ℝ =>
    (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1))]
  have hsimp : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
      Real.exp (-u) * ((-Real.log ((1 + Real.exp (-u)) - 1)) ^ l / (Nat.factorial l)
          * ((1 + Real.exp (-u)) - 1))
        = u ^ l / (Nat.factorial l) * Real.exp (-2 * u) := by
    intro u _
    simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
    rw [show Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) by
      rw [← Real.exp_add]; ring_nf]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsimp]
  have hfactor : ∀ u : ℝ, u ^ l / (Nat.factorial l) * Real.exp (-2 * u)
      = ((Nat.factorial l : ℝ))⁻¹ * (u ^ l * Real.exp (-2 * u)) := by
    intro u
    field_simp
  simp only [hfactor]
  rw [MeasureTheory.integral_const_mul]
  rw [show (fun a : ℝ => a ^ l * Real.exp (-2 * a))
      = fun a : ℝ => a ^ l * Real.exp (-(2 * a)) by
    funext a; ring_nf]
  rw [integral_pow_exp_neg_two_mul]
  have hfac : ((Nat.factorial l : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  field_simp

/-- Integrability of the (s-1)-weighted integrand on (1,2].
Under s = 1 + e^(-u) it becomes u^l/l! * e^(-2u), integrable on (0,inf).
This is the dominating integrand for bound (10). -/
theorem integrable_log_pow_sub_one (l : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1))
      (Set.Ioc (1 : ℝ) 2) := by
  apply integrableOn_Ioc_subst
  have hbase : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ l * Real.exp (-(2 * u))) (Set.Ioi (0 : ℝ)) :=
    integrable_pow_exp_two l
  have hconst := hbase.const_mul (((Nat.factorial l : ℝ))⁻¹)
  apply MeasureTheory.IntegrableOn.congr_fun hconst _ measurableSet_Ioi
  intro u hu
  simp only [add_sub_cancel_left, Real.log_exp, neg_neg]
  rw [show Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) by
    rw [← Real.exp_add]; ring_nf]
  field_simp

/-- MANUSCRIPT Theorem 6.1: S_2(m) = sum_{j+l=m} int_1^2 (-log(s-1))^l/l!
(s-1) 2^(-js) ds.  The (s-1)-weighted analogue of Sm. -/
noncomputable def S2m (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ∫ s in Set.Ioc (1 : ℝ) 2,
      (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (s - 1)
        * (2 : ℝ) ^ (-(j : ℝ) * s)

/-- The (s-1)-weighted inner sum of Dk at fixed i is exactly S2m (k-i).
S2m's definition sums over j <= m with log-index m - j; Dk's inner sum at
fixed i runs j <= k-i with log-index k-i-j.  With m = k-i these agree. -/
theorem inner_s2_group (k i : ℕ) (hik : i ≤ k) :
    ∑ j ∈ Finset.range (k - i + 1),
        (∫ s in Set.Ioc (1 : ℝ) 2,
          (-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)) * (s - 1)
            * (2 : ℝ) ^ (-(j : ℝ) * s))
      = S2m (k - i) := by
  unfold S2m
  rfl

/-- MANUSCRIPT Theorem 6.1: A^(2)_m = 2^m S_2(m). -/
noncomputable def A2m (m : ℕ) : ℝ := (2 : ℝ) ^ m * S2m m

/-- MANUSCRIPT Theorem 6.1: M_2(k) = sum bHat_i 2^i A^(2)_(k-i).

INDEXING DEVIATION: the manuscript sums i = 1..k, this sums i = 0..k.  The two
agree because bHat_0 = 0 -- every term of cBracket carries a factor of z
(the kappa part is z*(...), the prime terms are -z(z-1)log p/(...)), so
G2deriv1 f1 0 = 0.  That fact is TRUE but NOT PROVED here; proving it would
need the Cauchy formula in the direction we did not set up.  Anyone checking
these values against the Arb output should know the sums are indexed
differently. -/
noncomputable def M2k (f1 : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (bHat f1 i).re * (2 : ℝ) ^ i * A2m (k - i)

/-- M_2(k) in the S_2 form: 2^i A^(2)_(k-i) = 2^k S_2(k-i) for i <= k. -/
theorem M2k_eq_S2 (f1 : ℝ) (k : ℕ) :
    M2k f1 k = ∑ i ∈ Finset.range (k + 1),
      (2 : ℝ) ^ k * ((bHat f1 i).re * S2m (k - i)) := by
  unfold M2k A2m
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : (2 : ℝ) ^ i * (2 : ℝ) ^ (k - i) = (2 : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  calc (bHat f1 i).re * (2 : ℝ) ^ i * ((2 : ℝ) ^ (k - i) * S2m (k - i))
      = ((2 : ℝ) ^ i * (2 : ℝ) ^ (k - i)) * ((bHat f1 i).re * S2m (k - i)) := by ring
    _ = (2 : ℝ) ^ k * ((bHat f1 i).re * S2m (k - i)) := by rw [hpow]

/-- S_2's integrand is integrable on (1,2], dominated by the (s-1)-weighted
integrand of integrable_log_pow_sub_one since 2^(-js) <= 1 there. -/
theorem integrable_S2_integrand (l j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
        * (2 : ℝ) ^ (-(j : ℝ) * s))
      (Set.Ioc (1 : ℝ) 2) := by
  have hdom := integrable_log_pow_sub_one l
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
        * (2 : ℝ) ^ (-(j : ℝ) * s))
      (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2)) := by
    apply MeasureTheory.AEStronglyMeasurable.mul _ _
    · exact hdom.aestronglyMeasurable
    · apply Continuous.aestronglyMeasurable
      exact (continuous_const_rpow (by norm_num)).comp
        (continuous_const.mul continuous_id)
  apply MeasureTheory.Integrable.mono hdom hmeas
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
  have hs1 : (1 : ℝ) < s := hs.1
  have hs2 : s ≤ 2 := hs.2
  have hLpos : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) := by
    apply mul_nonneg _ (by linarith)
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  have h2 : (2 : ℝ) ^ (-(j : ℝ) * s) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    nlinarith [hs1]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLpos]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l
    / (Nat.factorial l) * (s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s))]
  exact mul_le_of_le_one_right hLpos h2

/-- Per-term identity: the E_1 term minus the M_2 term is 2^k times the
integral of the pointwise difference. -/
theorem term_diff_eq (i j l : ℕ) (f1 : ℝ) (K : ℝ)
    (hA : MeasureTheory.IntegrableOn
      (fun s : ℝ => ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) (Set.Ioc (1 : ℝ) 2)) :
    K * (∫ s in Set.Ioc (1 : ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
      - K * ((bHat f1 i).re * (∫ s in Set.Ioc (1 : ℝ) 2,
          (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
            * (2 : ℝ) ^ (-(j : ℝ) * s)))
      = K * (∫ s in Set.Ioc (1 : ℝ) 2,
          (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))
          - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))))) := by
  have hB : MeasureTheory.IntegrableOn
      (fun s : ℝ => (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))) (Set.Ioc (1 : ℝ) 2) := by
    have h := (integrable_S2_integrand l j).const_mul ((bHat f1 i).re)
    apply MeasureTheory.IntegrableOn.congr_fun h _ measurableSet_Ioc
    intro s _
    ring
  have hpull : (bHat f1 i).re * (∫ s in Set.Ioc (1 : ℝ) 2,
        (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
          * (2 : ℝ) ^ (-(j : ℝ) * s))
      = ∫ s in Set.Ioc (1 : ℝ) 2,
        (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro s _
    ring
  rw [hpull, ← mul_sub, ← MeasureTheory.integral_sub hA hB]

/-- The difference E_1(k) - M_2(k) as a double sum of per-term integrals. -/
theorem E1k_sub_M2k_eq (k : ℕ) (hk : 1 ≤ k) (f1 : ℝ) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    E1k k - M2k f1 k
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        ((2 : ℝ) ^ k * (∫ s in Set.Ioc (1 : ℝ) 2,
            (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
            - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))))) := by
  unfold E1k
  rw [Dk_eq_triple_sum k hk beta hbeta0 hderiv hbnd M0 hM00 hM0, M2k_eq_S2]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← inner_s2_group k i hik, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hAdiff : MeasureTheory.IntegrableOn
      (fun s : ℝ => ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
        * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))
      (Set.Ioc (1 : ℝ) 2) := by
    have hI := integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i)
      (hbnd i) M0 hM00 hM0
    have hF := (integrable_Sm_integrand (k - i - j) j).const_mul ((cCoeff i).re)
    have hFc : MeasureTheory.IntegrableOn
        (fun s : ℝ => (cCoeff i).re * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))
        (Set.Ioc (1 : ℝ) 2) := by
      apply MeasureTheory.IntegrableOn.congr_fun hF _ measurableSet_Ioc
      intro s _
      ring
    have hsub := hI.sub hFc
    apply MeasureTheory.IntegrableOn.congr_fun hsub _ measurableSet_Ioc
    intro s _
    simp only [Pi.sub_apply]
    ring
  exact term_diff_eq i j (k - i - j) f1 ((2 : ℝ) ^ k) hAdiff

/-- MANUSCRIPT THEOREM 6.1 (refined enclosure):
E_1(k) = M_2(k) + rho_2(k) with |rho_2(k)| <= Gamma, Gamma k-independent.
The k-independence is geom_two_three: sum_l 2^l 3^(-l-1) = 1 exactly. -/
theorem theorem_6_1 (k : ℕ) (hk : 1 ≤ k) (f1 : ℝ) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0)
    (gh : ℕ → ℝ) (hgh0 : ∀ i, 0 ≤ gh i)
    (htaylor : ∀ i : ℕ, ∀ s ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (gManu i s - cCoeff i - (((s - 1 : ℝ)) : ℂ) * bHat f1 i)
        ≤ gh i * (s - 1) ^ 2 / 2)
    (Gam : ℝ) (hGam : ∀ m : ℕ,
      (1 / 2) * ∑ i ∈ Finset.range (m + 1), gh i * (2 : ℝ) ^ i ≤ Gam) :
    |E1k k - M2k f1 k| ≤ Gam := by
  rw [E1k_sub_M2k_eq k hk f1 beta hbeta0 hderiv hbnd M0 hM00 hM0]
  have hstep : ∀ i ∈ Finset.range (k + 1),
      |∑ j ∈ Finset.range (k - i + 1),
        ((2 : ℝ) ^ k * (∫ s in Set.Ioc (1 : ℝ) 2,
            (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
            - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))))|
      ≤ gh i / 2 * (2 : ℝ) ^ i := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    have hterm : ∀ j ∈ Finset.range (k - i + 1),
        |(2 : ℝ) ^ k * (∫ s in Set.Ioc (1 : ℝ) 2,
            (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
            - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))))|
        ≤ gh i / 2 * ((2 : ℝ) ^ k
          * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))) := by
      intro j hj
      have hAdiff : MeasureTheory.IntegrableOn
          (fun s : ℝ => ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
            - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))
          (Set.Ioc (1 : ℝ) 2) := by
        have hI := integrable_Ik_term i j (k - i - j) (beta i) (hbeta0 i) (hderiv i)
          (hbnd i) M0 hM00 hM0
        have hF := (integrable_Sm_integrand (k - i - j) j).const_mul ((cCoeff i).re)
        have hFc : MeasureTheory.IntegrableOn
            (fun s : ℝ => (cCoeff i).re * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))
            (Set.Ioc (1 : ℝ) 2) := by
          apply MeasureTheory.IntegrableOn.congr_fun hF _ measurableSet_Ioc
          intro s _
          ring
        have hB := (integrable_S2_integrand (k - i - j) j).const_mul ((bHat f1 i).re)
        have hBc : MeasureTheory.IntegrableOn
            (fun s : ℝ => (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))
            (Set.Ioc (1 : ℝ) 2) := by
          apply MeasureTheory.IntegrableOn.congr_fun hB _ measurableSet_Ioc
          intro s _
          ring
        have hsub := (hI.sub hFc).sub hBc
        apply MeasureTheory.IntegrableOn.congr_fun hsub _ measurableSet_Ioc
        intro s _
        simp only [Pi.sub_apply]
        ring
      have hdom : MeasureTheory.IntegrableOn
          (fun s : ℝ => gh i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))
          (Set.Ioc (1 : ℝ) 2) := by
        have hbase := (integrable_log_pow_sub_one_sq (k - i - j)).const_mul (gh i / 2)
        have hmeas : MeasureTheory.AEStronglyMeasurable
            (fun s : ℝ => gh i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))
            (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2)) := by
          have hLsq := (integrable_log_pow_sub_one_sq (k - i - j)).aestronglyMeasurable
          have hexp : MeasureTheory.AEStronglyMeasurable
              (fun s : ℝ => (2 : ℝ) ^ (-(j : ℝ) * s))
              (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2)) :=
            (Continuous.aestronglyMeasurable
              ((continuous_const_rpow (by norm_num)).comp
                (continuous_const.mul continuous_id)))
          have hc := ((hLsq.mul hexp).const_mul (gh i / 2))
          apply hc.congr
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s _
          simp only [Pi.mul_apply]
          ring
        apply MeasureTheory.Integrable.mono hbase hmeas
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
        have hs1 : (1 : ℝ) < s := hs.1
        have hL : (0 : ℝ) ≤ (-Real.log (s - 1)) ^ (k - i - j)
            / (Nat.factorial (k - i - j)) := by
          apply div_nonneg _ (by positivity)
          apply pow_nonneg
          simp only [neg_nonneg]
          exact Real.log_nonpos (by linarith) (by linarith [hs.2])
        have h2 : (2 : ℝ) ^ (-(j : ℝ) * s) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          have : (0 : ℝ) ≤ (j : ℝ) := by positivity
          nlinarith [hs1]
        have h2p : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
        have hbig : (0 : ℝ) ≤ gh i / 2 * ((-Real.log (s - 1)) ^ (k - i - j)
            / (Nat.factorial (k - i - j)) * (s - 1) ^ 2) := by
          apply mul_nonneg (by linarith [hgh0 i])
          apply mul_nonneg hL (sq_nonneg _)
        have hsmall : (0 : ℝ) ≤ gh i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
            * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
          apply mul_nonneg
          · apply div_nonneg _ (by norm_num)
            exact mul_nonneg (hgh0 i) (sq_nonneg _)
          · exact mul_nonneg (le_of_lt h2p) hL
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsmall, abs_of_nonneg hbig]
        nlinarith [hL, h2, h2p, hgh0 i, sq_nonneg (s - 1)]
      have hint : |∫ s in Set.Ioc (1 : ℝ) 2,
            (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
            - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))|
          ≤ ∫ s in Set.Ioc (1 : ℝ) 2,
            gh i * (s - 1) ^ 2 / 2 * ((2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))) := by
        rw [← Real.norm_eq_abs]
        apply MeasureTheory.norm_integral_le_of_norm_le hdom
        have hnull : (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2))
            (Set.Ioc (1 : ℝ) 2 \ Set.Ioo (1 : ℝ) 2) = 0 := by
          have hsing : Set.Ioc (1 : ℝ) 2 \ Set.Ioo (1 : ℝ) 2 ⊆ {(2 : ℝ)} := by
            intro x hx
            simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo,
              Set.mem_singleton_iff] at hx ⊢
            rcases hx with ⟨⟨h1, h2⟩, h3⟩
            by_contra hne
            exact h3 ⟨h1, lt_of_le_of_ne h2 hne⟩
          exact MeasureTheory.measure_mono_null hsing (by simp)
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
          MeasureTheory.compl_mem_ae_iff.mpr hnull] with s hs hs2
        have hsIoo : s ∈ Set.Ioo (1 : ℝ) 2 := by
          by_contra hcon
          exact hs2 (Set.mem_sdiff_of_mem hs hcon)
        rw [Real.norm_eq_abs]
        exact Dk_term_split i j (k - i - j) f1 (gh i) (hgh0 i) (htaylor i) s hsIoo
      have hrem := Dk_remainder_term_le j (k - i - j) (gh i) (hgh0 i)
      have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
      rw [abs_mul, abs_of_nonneg h2k]
      calc (2 : ℝ) ^ k * |∫ s in Set.Ioc (1 : ℝ) 2,
              (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
                * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
              - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
                * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))|
          ≤ (2 : ℝ) ^ k * (gh i / 2 * ((2 : ℝ) ^ (-(j : ℝ))
              * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))) := by
            apply mul_le_mul_of_nonneg_left _ h2k
            exact le_trans hint hrem
        _ = gh i / 2 * ((2 : ℝ) ^ k
            * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))) := by ring
    calc ∑ j ∈ Finset.range (k - i + 1),
          |(2 : ℝ) ^ k * (∫ s in Set.Ioc (1 : ℝ) 2,
              (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
                * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
              - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
                * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))))|
        ≤ ∑ j ∈ Finset.range (k - i + 1),
            gh i / 2 * ((2 : ℝ) ^ k
              * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))) :=
          Finset.sum_le_sum hterm
      _ = gh i / 2 * ∑ j ∈ Finset.range (k - i + 1),
            ((2 : ℝ) ^ k * ((2 : ℝ) ^ (-(j : ℝ)) * (1 / (3 : ℝ) ^ ((k - i - j) + 1)))) := by
          rw [Finset.mul_sum]
      _ ≤ gh i / 2 * (2 : ℝ) ^ i := by
          apply mul_le_mul_of_nonneg_left (remainder_inner_le k i hik)
          linarith [hgh0 i]
  calc |∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        ((2 : ℝ) ^ k * (∫ s in Set.Ioc (1 : ℝ) 2,
            (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))
            - (bHat f1 i).re * ((s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
              * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)))))))|
      ≤ ∑ i ∈ Finset.range (k + 1), gh i / 2 * (2 : ℝ) ^ i := by
        apply le_trans (Finset.abs_sum_le_sum_abs _ _)
        exact Finset.sum_le_sum hstep
    _ = (1 / 2) * ∑ i ∈ Finset.range (k + 1), gh i * (2 : ℝ) ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ Gam := hGam k

/-- Per-term bound for S_2: the j-th term is at most 2^(-j) 2^(-l-1).
Uses 2^(-js) <= 2^(-j) on [1,2] and the exact integral
integral_log_pow_sub_one. -/
theorem S2_term_le (l j : ℕ) :
    (∫ s in Set.Ioc (1 : ℝ) 2,
      (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
        * (2 : ℝ) ^ (-(j : ℝ) * s))
      ≤ (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ (l + 1)) := by
  have hleft := integrable_S2_integrand l j
  have hright := (integrable_log_pow_sub_one l).const_mul ((2 : ℝ) ^ (-(j : ℝ)))
  have hL : ∀ s : ℝ, s ∈ Set.Ioc (1 : ℝ) 2 →
      (0 : ℝ) ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) := by
    intro s hs
    apply mul_nonneg _ (by linarith [hs.1])
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    simp only [neg_nonneg]
    exact Real.log_nonpos (by linarith [hs.1]) (by linarith [hs.2])
  have hmono : (∫ s in Set.Ioc (1 : ℝ) 2,
        (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)
          * (2 : ℝ) ^ (-(j : ℝ) * s))
      ≤ ∫ s in Set.Ioc (1 : ℝ) 2,
        (2 : ℝ) ^ (-(j : ℝ)) * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hright ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
      exact mul_nonneg (hL s hs) (le_of_lt h2)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hmonoexp : (2 : ℝ) ^ (-(j : ℝ) * s) ≤ (2 : ℝ) ^ (-(j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        nlinarith [hs.1]
      calc (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) * (2 : ℝ) ^ (-(j : ℝ) * s)
          ≤ (-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1) * (2 : ℝ) ^ (-(j : ℝ)) :=
            mul_le_mul_of_nonneg_left hmonoexp (hL s hs)
        _ = (2 : ℝ) ^ (-(j : ℝ))
            * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by ring
  rw [MeasureTheory.integral_const_mul, integral_log_pow_sub_one] at hmono
  exact hmono

theorem Dk_term_bound (i j l : ℕ) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hderiv : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    |∫ s in Set.Ioc (1 : ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l))|
      ≤ beta * (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ (l + 1)) := by
  have hdom := (integrable_log_pow_sub_one l).const_mul (beta * (2 : ℝ) ^ (-(j : ℝ)))
  have hae : ∀ᵐ s ∂ (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2)),
      Norm.norm (((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l)))
        ≤ beta * (2 : ℝ) ^ (-(j : ℝ))
          * ((-Real.log (s - 1)) ^ l / (Nat.factorial l) * (s - 1)) := by
    have hIoo : (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2))
        (Set.Ioc (1 : ℝ) 2 \ Set.Ioo (1 : ℝ) 2) = 0 := by
      have : Set.Ioc (1 : ℝ) 2 \ Set.Ioo (1 : ℝ) 2 ⊆ {(2 : ℝ)} := by
        intro x hx
        simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff] at hx ⊢
        rcases hx with ⟨ ⟨ h1, h2 ⟩, h3 ⟩
        by_contra hne
        exact h3 ⟨ h1, lt_of_le_of_ne h2 hne ⟩
      exact MeasureTheory.measure_mono_null this (by simp)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      MeasureTheory.compl_mem_ae_iff.mpr hIoo] with s hs hs2
    have hsIoo : s ∈ Set.Ioo (1 : ℝ) 2 := by
      by_contra hcon
      exact hs2 (Set.mem_sdiff_of_mem hs hcon)
    rw [Real.norm_eq_abs]
    exact Dk_integrand_ptwise i j l beta hbeta0 hderiv hbnd M0 hM00 hM0 s hsIoo
  have hle := MeasureTheory.norm_integral_le_of_norm_le hdom hae
  rw [Real.norm_eq_abs] at hle
  rw [MeasureTheory.integral_const_mul, integral_log_pow_sub_one] at hle
  exact hle


/-- The inner sum of (10) is constant in j: each term is 2^(-(k-i)-1),
so the sum over j <= k-i is (k-i+1) * 2^(-(k-i)-1). -/
theorem inner_sum_const (k i : ℕ) (hik : i ≤ k) (b : ℝ) :
    ∑ j ∈ Finset.range (k - i + 1),
        b * (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ ((k - i - j) + 1))
      = ((k : ℝ) - (i : ℝ) + 1) * (b * (1 / (2 : ℝ) ^ ((k - i) + 1))) := by
  have hterm : ∀ j ∈ Finset.range (k - i + 1),
      b * (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ ((k - i - j) + 1))
        = b * (1 / (2 : ℝ) ^ ((k - i) + 1)) := by
    intro j hj
    have hjk : j ≤ k - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : (2 : ℝ) ^ (-(j : ℝ)) = 1 / (2 : ℝ) ^ (j : ℕ) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      ring
    rw [hpow]
    have hsplit : (2 : ℝ) ^ ((k - i) + 1) = (2 : ℝ) ^ (j : ℕ) * (2 : ℝ) ^ ((k - i - j) + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
  rw [nsmul_eq_mul]
  congr 1
  have : ((k - i + 1 : ℕ) : ℝ) = (k : ℝ) - (i : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hik]
    norm_num
  exact this

/-- MANUSCRIPT Theorem 6.1: A^(2)_m <= (m+1)/2.
Each term of S_2(m) is at most 2^(-j) 2^(-(m-j)-1) = 2^(-m-1), constant in j;
there are m+1 of them, and multiplying by 2^m gives (m+1)/2. -/
theorem A2m_le (m : ℕ) : A2m m ≤ ((m : ℝ) + 1) / 2 := by
  have hbound : S2m m ≤ ∑ j ∈ Finset.range (m + 1),
      (1 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ ((m - j) + 1)) := by
    unfold S2m
    apply Finset.sum_le_sum
    intro j _
    have h := S2_term_le (m - j) j
    calc (∫ s in Set.Ioc (1 : ℝ) 2,
          (-Real.log (s - 1)) ^ (m - j) / (Nat.factorial (m - j)) * (s - 1)
            * (2 : ℝ) ^ (-(j : ℝ) * s))
        ≤ (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ ((m - j) + 1)) := h
      _ = (1 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) * (1 / (2 : ℝ) ^ ((m - j) + 1)) := by ring
  have hconst := inner_sum_const m 0 (Nat.zero_le m) (1 : ℝ)
  simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at hconst
  rw [hconst] at hbound
  unfold A2m
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hstep : (2 : ℝ) ^ m * S2m m
      ≤ (2 : ℝ) ^ m * (((m : ℝ) + 1) * ((1 : ℝ) * (1 / (2 : ℝ) ^ (m + 1)))) :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt h2m)
  have hval : (2 : ℝ) ^ m * (((m : ℝ) + 1) * ((1 : ℝ) * (1 / (2 : ℝ) ^ (m + 1))))
      = ((m : ℝ) + 1) / 2 := by
    rw [pow_succ]
    field_simp
  linarith [hstep, hval]

/-- MANUSCRIPT (10): |E_1(k)| <= (1 / 2) sum_{i<=k} beta_i 2^i (k-i+1).
The inner sum over j is constant in j -- 2^(-j) * 2^(-(k-i-j)-1) = 2^(-(k-i)-1)
-- so it contributes a factor (k-i+1), and 2^k * 2^(-(k-i)-1) = 2^(i-1). -/
theorem E1k_bound (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0) :
    |E1k k| ≤ (1 / 2) * ∑ i ∈ Finset.range (k + 1),
      beta i * (2 : ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1) := by
  unfold E1k
  rw [Dk_eq_triple_sum k hk beta hbeta0 hderiv hbnd M0 hM00 hM0]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
  have hstep : |∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
      (∫ s in Set.Ioc (1 : ℝ) 2,
        ((gManu i s).re - (cCoeff i).re) * (2 : ℝ) ^ (-(j : ℝ) * s)
          * ((-Real.log (s - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j))))|
      ≤ ∑ i ∈ Finset.range (k + 1),
          ((k : ℝ) - (i : ℝ) + 1) * (beta i * (1 / (2 : ℝ) ^ ((k - i) + 1))) := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply Finset.sum_le_sum
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    rw [← inner_sum_const k i hik (beta i)]
    apply Finset.sum_le_sum
    intro j _
    exact Dk_term_bound i j (k - i - j) (beta i) (hbeta0 i) (hderiv i) (hbnd i)
      M0 hM00 hM0
  apply le_trans (mul_le_mul_of_nonneg_left hstep (by positivity))
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : (2 : ℝ) ^ k * (1 / (2 : ℝ) ^ ((k - i) + 1)) = (2 : ℝ) ^ i / 2 := by
    have hsplit : (2 : ℝ) ^ k = (2 : ℝ) ^ i * (2 : ℝ) ^ (k - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, pow_succ]
    field_simp
  calc (2 : ℝ) ^ k * (((k : ℝ) - (i : ℝ) + 1) * (beta i * (1 / (2 : ℝ) ^ ((k - i) + 1))))
      = ((k : ℝ) - (i : ℝ) + 1) * beta i * ((2 : ℝ) ^ k * (1 / (2 : ℝ) ^ ((k - i) + 1))) := by ring
    _ = ((k : ℝ) - (i : ℝ) + 1) * beta i * ((2 : ℝ) ^ i / 2) := by rw [hpow]
    _ = 1 / 2 * (beta i * (2 : ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1)) := by ring
    _ ≤ 1 / 2 * (beta i * (2 : ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1)) := le_refl _

/-- MANUSCRIPT section 3.5: |E_1(k)| <= alpha_+ (k+1).
From (10), since (k-i+1) <= (k+1) for every i in the sum.  alpha_+ bounds
(1 / 2) sum_{i<=k} beta_i 2^i uniformly in k -- the manuscript evaluates it by
splitting at 30 and using the Cauchy tail beta_i <= M1 / 2.9^i, which is a
certified computation, so it enters here as a hypothesis. -/
theorem E1k_le_alpha (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → ℝ)
    (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0)
    (alpha : ℝ) (halpha : ∀ m : ℕ,
      (1 / 2) * ∑ i ∈ Finset.range (m + 1), beta i * (2 : ℝ) ^ i ≤ alpha) :
    |E1k k| ≤ alpha * ((k : ℝ) + 1) := by
  have hb := E1k_bound k hk beta hbeta0 hderiv hbnd M0 hM00 hM0
  have hstep : (1 / 2) * ∑ i ∈ Finset.range (k + 1),
        beta i * (2 : ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1)
      ≤ ((k : ℝ) + 1) * ((1 / 2) * ∑ i ∈ Finset.range (k + 1), beta i * (2 : ℝ) ^ i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hikR : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
    have hnn : (0 : ℝ) ≤ beta i * (2 : ℝ) ^ i := by
      apply mul_nonneg (hbeta0 i)
      positivity
    have hfac : (k : ℝ) - (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by linarith
    nlinarith [hnn, hfac]
  calc |E1k k| ≤ (1 / 2) * ∑ i ∈ Finset.range (k + 1),
        beta i * (2 : ℝ) ^ i * ((k : ℝ) - (i : ℝ) + 1) := hb
    _ ≤ ((k : ℝ) + 1) * ((1 / 2) * ∑ i ∈ Finset.range (k + 1),
        beta i * (2 : ℝ) ^ i) := hstep
    _ ≤ ((k : ℝ) + 1) * alpha := by
        apply mul_le_mul_of_nonneg_left (halpha k)
        positivity
    _ = alpha * ((k : ℝ) + 1) := by ring


/-- source_bound_derived with the E_1 hypothesis discharged by E1k_le_alpha.

The section 3.5 inputs (beta_i, the derivative bounds, M_0) now appear
explicitly, which is honest: they are certified numerics, and having them at
the top is better than hiding them behind an aggregate assumption on E_1. -/
theorem source_bound_full (k : ℕ) (hk : 1 ≤ k)
    (Sstar alph Umax Vmax : ℝ)
    (beta : ℕ → ℝ) (hbeta0 : ∀ i, 0 ≤ beta i)
    (hderiv : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x)
    (hbnd : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i)
    (M0 : ℝ) (hM00 : 0 ≤ M0)
    (hM0 : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
      Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0)
    (halpha : ∀ m : ℕ,
      (1 / 2) * ∑ i ∈ Finset.range (m + 1), beta i * (2 : ℝ) ^ i ≤ alph)
    (hS : ∀ m : ℕ,
      ∑ i ∈ Finset.range (m + 1), (2:ℝ) ^ i * |(cCoeff i).re| ≤ Sstar)
    (hUV : |2 * (2 * (k : ℝ) * Uk k - Vk k)
             - (2 * ((k : ℝ) + 1) * Uk (k + 1) - Vk (k + 1))|
           ≤ (2 * (k : ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax)
    (hEexp : ∀ m : ℕ, |Eexpk m| ≤ 1.45 / (k : ℝ) + 1e-3) :
    |2 * Ek k - Ek (k + 1)| ≤ RBound Umax Vmax Sstar alph k :=
  source_bound_derived k hk Sstar alph Umax Vmax hS
    (fun m hm => E1k_le_alpha m hm beta hbeta0 hderiv hbnd M0 hM00 hM0 alph halpha)
    hUV hEexp

theorem lemma_3_8_integral_r1 (i : ℕ) (s : ℝ) (hsmem : s ∈ Set.Ioo (1 : ℝ) 2)
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Ioo (1 : ℝ) 2,
      HasDerivAt (fun t : ℝ => Real.log (zetaTilde t)) (f x) x)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Ioo (1 : ℝ) 2, ∀ theta : ℝ,
      Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) x) ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ theta in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2manu t (circleMap 0 (2 : ℝ) theta))))
      (∫ theta in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap 0 (2 : ℝ)) theta
          * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
            * ((circleMap 0 (2 : ℝ) theta)⁻¹
              * deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) s))) s := by
  have hkap : ∀ x ∈ Set.Ioo (1 : ℝ) 2, 0 < kappaFac x :=
    fun x hx => kappaFac_pos x hx.1 (cFac_pos x hx.1)
  have hnhds : Set.Ioo (1 : ℝ) 2 ∈ nhds s := Ioo_mem_nhds hsmem.1 hsmem.2
  have hcont : ∀ x ∈ Set.Ioo (1 : ℝ) 2, Continuous (fun theta : ℝ =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2manu x (circleMap 0 (2 : ℝ) theta)))) :=
    fun x hx => contour_integrand_continuous x (le_of_lt hx.1) (hkap x hx) i
  have hnorm2 : ∀ theta : ℝ, Norm.norm (circleMap 0 (2 : ℝ) theta) ≤ 2 := by
    intro theta
    simp [circleMap]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℝ) (theta : ℝ) =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹ * G2manu x (circleMap 0 (2 : ℝ) theta))))
    (F' := fun (x : ℝ) (theta : ℝ) =>
      deriv (circleMap 0 (2 : ℝ)) theta
        * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
          * ((circleMap 0 (2 : ℝ) theta)⁻¹
            * deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) x)))
    (bound := fun _ => M) (x₀ := s) (s := Set.Ioo (1 : ℝ) 2)
    hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hnhds] with x hx
    exact (hcont x hx).aestronglyMeasurable
  · exact ((hcont s hsmem).intervalIntegrable 0 (2 * Real.pi))
  · have hcm : Continuous (circleMap 0 (2 : ℝ)) := continuous_circleMap 0 _
    have hR : (0 : ℝ) < 2 := by norm_num
    have hne : ∀ t : ℝ, circleMap 0 (2 : ℝ) t ≠ 0 :=
      fun t => circleMap_ne_center (ne_of_gt hR)
    have hdcm : Continuous (deriv (circleMap 0 (2 : ℝ))) := by
      have hd : deriv (circleMap 0 (2 : ℝ))
          = fun t => circleMap 0 (2 : ℝ) t * Complex.I := by
        funext t
        exact deriv_circleMap 0 (2 : ℝ) t
      rw [hd]
      exact hcm.mul continuous_const
    apply Continuous.aestronglyMeasurable
    apply hdcm.mul
    apply Continuous.mul
    · exact (continuous_const.div hcm (fun t => hne t)).pow i
    · exact (hcm.inv₀ (fun t => hne t)).mul
        (G2manu_deriv_continuous_theta s hsmem f hf)
  · filter_upwards with theta _ x hx
    exact contour_integrand_deriv_bound i M hM0 x theta (hM x hx theta)
  · exact intervalIntegrable_const
  · filter_upwards with theta _ x hx
    have hd := lemma_3_9_complex (circleMap 0 (2 : ℝ) theta) (hnorm2 theta) x hx f (hf x hx)
    rw [hd.deriv]
    exact ((hd.const_mul _).const_mul _).const_mul _


/-- MANUSCRIPT THEOREM 1.1: f_k < f_(k+1) for every k >= 6.

The four ranges of the manuscript, in order:
  [6, 199]      sweep_low   -- the prior certified f_k computation
  [78, 899]     sweep_mid   -- Theorem 6.2's refined criterion sweep (K0 = 78)
  [900, 2439]   sweep_high  -- the extended delta-table sweep of section 5
  [2440, inf)   theorem_7_1 -- the derivative-domination argument, PROVED here

The union is [6, inf) with no gaps.  Everything outside theorem_7_1 is a
certified computation entering through NumericalFacts. -/
theorem erdos_sums_increase_from_six (Sstar alph Gam Umax Vmax : ℝ)
    (hnum : NumericalFacts Sstar alph Gam Umax Vmax) :
    ∀ k : ℕ, 6 ≤ k → f k < f (k + 1) := by
  intro k hk
  by_cases h1 : k ≤ 199
  · exact hnum.sweep_low k hk h1
  by_cases h2 : k ≤ 899
  · exact hnum.sweep_mid k (by omega) h2
  by_cases h3 : k ≤ 2439
  · exact hnum.sweep_high k (by omega) h3
  · exact theorem_7_1 aOneConst Umax Vmax Sstar alph 2440
      (phiBound_pos_at_2440 aOneConst Umax Vmax Sstar alph
          aOneConst_ge
          hnum.Umax_nonneg hnum.U_bound
          hnum.Vmax_nonneg hnum.V_bound
          hnum.Sstar_nonneg hnum.Sstar_bound
          hnum.alph_nonneg hnum.alpha_bound)
        (phiBound_mono_of_bounds aOneConst Umax Vmax Sstar alph
          aOneConst_ge
          hnum.Umax_nonneg hnum.U_bound
          hnum.Sstar_nonneg hnum.Sstar_bound
          hnum.alph_nonneg hnum.alpha_bound)
        hnum.source_bound k (by omega)

end

#print axioms erdos_sums_increase_from_six

/-- `g_deriv` is DERIVABLE from a sup bound on the s-derivative.

`NumericalFactsFull.g_deriv` assumes

    forall i, forall x in Ioo 1 2, HasDerivAt (gManu i) (deriv (gManu i) x) x

which is `DifferentiableAt R (gManu i) x` in disguise -- a limit existing, not
an interval enclosure, so no Arb run establishes it and no recomputation closes
it (see the CAUTION on `NumericalFactsFull`).  This theorem replaces it with a
hypothesis of the kind Arb DOES compute: a uniform bound on the s-derivative of
`G2manu` on the integration circle.

The route is assembled from pieces already in this file:

  * `gManu_eq_circleIntegral` rewrites `gManu i t` as a contour integral over
    |z| = 2 in which the t-dependence sits only in `G2manu t z`; the
    `(1/z)^i * z⁻¹` weight is s-free, which is what makes differentiating under
    the integral clean.
  * `lemma_3_8_integral_r1` differentiates under exactly that integral, given
    `hf` and the sup bound `hM`.
  * `log_zetaTilde_hasDerivAt` supplies `hf`, which was previously threaded
    through unproved.

So the only genuinely assumed input left is `hM1`, and unlike `g_deriv` it is a
numerical statement: the sup of a derivative over a compact circle and a
bounded s-range.  Substituting it for `g_deriv` makes the structure's docstring
true, which is the point -- it does not reduce the field count, it moves one
field from the wrong side of Section 8's line to the right side. -/
theorem g_deriv_of_derivBound (M1 : ℝ) (hM10 : 0 ≤ M1)
    (hM1 : ∀ x ∈ Set.Ioo (1 : ℝ) 2, ∀ theta : ℝ,
      Norm.norm (deriv (fun u : ℝ => G2manu u (circleMap 0 (2 : ℝ) theta)) x) ≤ M1)
    (i : ℕ) (x : ℝ) (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x := by
  -- the contour form, for every t > 1; idiom taken from gManu_tendsto_cCoeff's proof
  have hci : ∀ t : ℝ, 1 < t →
      gManu i t = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (∫ theta in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap 0 (2 : ℝ)) theta
            * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
              * ((circleMap 0 (2 : ℝ) theta)⁻¹
                * G2manu t (circleMap 0 (2 : ℝ) theta)))) := by
    intro t ht
    have hkap : 0 < kappaFac t := kappaFac_pos t ht (cFac_pos t ht)
    rw [gManu_eq_circleIntegral t (le_of_lt ht) hkap i]
    unfold circleIntegral
    simp only [smul_eq_mul]
  -- differentiate under the integral, with hf now proved rather than assumed
  have hI := lemma_3_8_integral_r1 i x hx
    (deriv (fun t : ℝ => Real.log (zetaTilde t)))
    (fun y hy => log_zetaTilde_hasDerivAt y hy) M1 hM10 hM1
  have hscaled := hI.const_smul (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
  -- gManu agrees with the scaled integral on a neighbourhood of x
  have hev : (fun t : ℝ => gManu i t) =ᶠ[nhds x]
      (fun t : ℝ => (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)⁻¹
        • (∫ theta in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap 0 (2 : ℝ)) theta
            * ((1 / circleMap 0 (2 : ℝ) theta) ^ i
              * ((circleMap 0 (2 : ℝ) theta)⁻¹
                * G2manu t (circleMap 0 (2 : ℝ) theta))))) := by
    refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx.1) ?_
    intro t ht
    exact hci t ht
  exact (hscaled.congr_of_eventuallyEq hev).differentiableAt.hasDerivAt

/-- The certified inputs, decomposed into primitives.

`NumericalFacts` above states the section 7 source bound as a single aggregate.
This version replaces it with the quantities the Arb package actually computes,
so that Proposition 2.5, Theorem 4.1 and section 3.5 are *used* in deriving it
rather than merely proved.

CAUTION about `g_deriv`.  `NumericalFacts`'s docstring says "each field is an
Arb ball computation", and for this structure that is NOT true of every field.
`g_deriv` asserts

    forall i, forall x in Ioo 1 2, HasDerivAt (gManu i) (deriv (gManu i) x) x

which is equivalent to `DifferentiableAt R (gManu i) x` -- if `gManu i` were
not differentiable at `x` then `deriv (gManu i) x = 0` and the field would be
false.  So this is a DIFFERENTIABILITY claim, not a numerical enclosure, and
no interval computation establishes it: an Arb run bounds a quantity, it does
not show a limit exists.  It is load-bearing (used via `source_bound_full`),
so it cannot be dropped the way `Gamma_bound` can.

The remedy is therefore a proof rather than a recomputation, and the proof is
a real one: `G2manu s z = (kappaFac s)^z * G2C s z`, so `gManu i s` is the
i-th z-derivative at 0 of that product divided by i!, and differentiating it
in `s` means differentiating an Euler product under the iterated-derivative
operator.  That is the same order of work as `source_bound`.


Recorded because the distinction changes who owns the obligation: a numerical
field is closed by rerunning the certified package, an analytic one is not. -/
structure NumericalFactsFull (beta : ℕ → ℝ) (Sstar alph Gam Umax Vmax M0 : ℝ) : Prop where
  /-- See the note on `NumericalFacts.Sstar_bound`: 6.9763 was not an upper
  bound for the certified 6.97633273. -/
  Sstar_bound   : Sstar ≤ 6.9764
  alpha_bound   : alph ≤ 15.4257
  Gamma_bound   : Gam ≤ 104.52
  beta_nonneg   : ∀ i, 0 ≤ beta i
  /-- NOT a numerical fact -- see the CAUTION in this structure's docstring.
  This is `DifferentiableAt R (gManu i) x` in disguise, and no Arb computation
  can establish it. -/
  g_deriv       : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
    HasDerivAt (fun t : ℝ => gManu i t) (deriv (fun t : ℝ => gManu i t) x) x
  g_deriv_bound : ∀ i : ℕ, ∀ x ∈ Set.Ioo (1 : ℝ) 2,
    Norm.norm (deriv (fun t : ℝ => gManu i t) x) ≤ beta i
  M0_nonneg     : 0 ≤ M0
  M0_bound      : ∀ u : ℝ, u ∈ Set.Ioi (1 : ℝ) → ∀ theta : ℝ,
    Norm.norm (G2manu u (circleMap 0 (2 : ℝ) theta)) ≤ M0
  alpha_dom     : ∀ m : ℕ,
    (1 / 2) * ∑ i ∈ Finset.range (m + 1), beta i * (2 : ℝ) ^ i ≤ alph
  Sstar_dom     : ∀ m : ℕ,
    ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * |(cCoeff i).re| ≤ Sstar
  UV_bound      : ∀ k : ℕ, 2440 ≤ k →
    |2 * (2 * (k : ℝ) * Uk k - Vk k)
       - (2 * ((k : ℝ) + 1) * Uk (k + 1) - Vk (k + 1))|
    ≤ (2 * (k : ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax
  /-- Section 7: the exponentially small source, at the two indices used. -/
  Eexp_bound    : ∀ k : ℕ, 2440 ≤ k → ∀ m : ℕ,
    |Eexpk m| ≤ 1.45 / (k : ℝ) + 1e-3
  /-- `phi_mono` stood here.  It is now proved -- `phiBound_mono_of_bounds` --
  and what it needed that this structure did not carry is an upper bound on
  `Umax`, which the manuscript states as `|U| <= 0.08436`.  The three
  nonnegativity fields are free in any instantiation: all of these parameters
  are bounds on absolute values.  A universally quantified assumption about a
  quadratic, which no finite computation can discharge and no reader can check
  by inspection, is replaced by scalars `verify.py` can check. -/
  Umax_nonneg   : 0 ≤ Umax
  U_bound       : Umax ≤ 0.08436
  Vmax_nonneg   : 0 ≤ Vmax
  V_bound       : Vmax ≤ 1.90747
  Sstar_nonneg  : 0 ≤ Sstar
  alph_nonneg   : 0 ≤ alph
  sweep_low     : ∀ k : ℕ, 6 ≤ k → k ≤ 199 → f k < f (k + 1)
  sweep_mid     : ∀ k : ℕ, 78 ≤ k → k ≤ 899 → f k < f (k + 1)
  sweep_high    : ∀ k : ℕ, 900 ≤ k → k ≤ 2439 → f k < f (k + 1)

/-- MANUSCRIPT THEOREM 1.1, with the far range derived from the primitives.

Identical in statement to `erdos_sums_increase_from_six`, but the [2440, inf)
branch goes through `source_bound_full`, so the dependency chain reaches
Proposition 2.5 (the exact decomposition), Theorem 4.1 (via `deltaM_abs_le`
and `deltaConv_le`) and section 3.5 (via `E1k_le_alpha`). -/
theorem erdos_sums_increase_from_six' (beta : ℕ → ℝ)
    (Sstar alph Gam Umax Vmax M0 : ℝ)
    (hnum : NumericalFactsFull beta Sstar alph Gam Umax Vmax M0) :
    ∀ k : ℕ, 6 ≤ k → f k < f (k + 1) := by
  intro k hk
  by_cases h1 : k ≤ 199
  · exact hnum.sweep_low k hk h1
  by_cases h2 : k ≤ 899
  · exact hnum.sweep_mid k (by omega) h2
  by_cases h3 : k ≤ 2439
  · exact hnum.sweep_high k (by omega) h3
  · refine theorem_7_1 aOneConst Umax Vmax Sstar alph 2440
      (phiBound_pos_at_2440 aOneConst Umax Vmax Sstar alph
          aOneConst_ge
          hnum.Umax_nonneg hnum.U_bound
          hnum.Vmax_nonneg hnum.V_bound
          hnum.Sstar_nonneg hnum.Sstar_bound
          hnum.alph_nonneg hnum.alpha_bound)
        (phiBound_mono_of_bounds aOneConst Umax Vmax Sstar alph
          aOneConst_ge
          hnum.Umax_nonneg hnum.U_bound
          hnum.Sstar_nonneg hnum.Sstar_bound
          hnum.alph_nonneg hnum.alpha_bound)
        ?_ k (by omega)
    intro m hm
    exact source_bound_full m (by omega) Sstar alph Umax Vmax beta hnum.beta_nonneg
      hnum.g_deriv hnum.g_deriv_bound M0 hnum.M0_nonneg hnum.M0_bound
      hnum.alpha_dom hnum.Sstar_dom (hnum.UV_bound m hm) (hnum.Eexp_bound m hm)

/-- cBracket vanishes at z = 0: every term carries a factor of z.

This is the algebraic content behind bHat_0 = 0.  Getting from here to
`bHat f1 0 = 0` needs the Cauchy formula (the 0th coefficient equals the value
at the centre), which this development deliberately avoids -- bHat is defined
as a contour integral precisely so that z-analyticity of cBracket is not
required.  So bHat_0 = 0 is TRUE and follows from this, but is NOT proved here;
M2k's indexing from i = 0 rather than the manuscript's i = 1 relies on it. -/
theorem cBracket_at_zero (fs s : ℝ) : cBracket fs s 0 = 0 := by
  unfold cBracket
  simp

/-- |M_2(k)| <= (Bhat/2)(k+1), where Bhat dominates sum |bHat_i| 2^i.
Uses A2m_le: A^(2)_m <= (m+1)/2. -/
theorem M2k_le (f1 : ℝ) (k : ℕ) (Bhat : ℝ)
    (hB : ∑ i ∈ Finset.range (k + 1), |(bHat f1 i).re| * (2 : ℝ) ^ i ≤ Bhat) :
    |M2k f1 k| ≤ Bhat * ((k : ℝ) + 1) / 2 := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(bHat f1 i).re * (2 : ℝ) ^ i * A2m (k - i)|
        ≤ (|(bHat f1 i).re| * (2 : ℝ) ^ i) * (((k : ℝ) + 1) / 2) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hA := A2m_le (k - i)
    have hcast : ((k - i : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have h : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : (k - i : ℕ) ≤ k := by omega
        exact_mod_cast this
      linarith
    have hA' : A2m (k - i) ≤ ((k : ℝ) + 1) / 2 := by linarith
    have hA0 : (0 : ℝ) ≤ A2m (k - i) := by
      unfold A2m
      have h1 : (0:ℝ) ≤ (2:ℝ) ^ (k - i) := by positivity
      have h2 : (0:ℝ) ≤ S2m (k - i) := by
        unfold S2m
        apply Finset.sum_nonneg
        intro j _
        apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
        intro x hx
        have hx1 : (1:ℝ) < x := hx.1
        have hL : (0:ℝ) ≤ (-Real.log (x - 1)) ^ (k - i - j) / (Nat.factorial (k - i - j)) := by
          apply div_nonneg _ (by positivity)
          apply pow_nonneg
          simp only [neg_nonneg]
          exact Real.log_nonpos (by linarith) (by linarith [hx.2])
        have hs1 : (0:ℝ) ≤ x - 1 := by linarith
        have h2p : (0:ℝ) < (2:ℝ) ^ (-(j:ℝ) * x) := Real.rpow_pos_of_pos (by norm_num) _
        exact mul_nonneg (mul_nonneg hL hs1) (le_of_lt h2p)
      positivity
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
    calc |(bHat f1 i).re * (2 : ℝ) ^ i * A2m (k - i)|
        = (|(bHat f1 i).re| * (2 : ℝ) ^ i) * |A2m (k - i)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h2]
      _ = (|(bHat f1 i).re| * (2 : ℝ) ^ i) * A2m (k - i) := by rw [abs_of_nonneg hA0]
      _ ≤ (|(bHat f1 i).re| * (2 : ℝ) ^ i) * (((k : ℝ) + 1) / 2) := by
          apply mul_le_mul_of_nonneg_left hA' (by positivity)
  unfold M2k
  calc |∑ i ∈ Finset.range (k + 1), (bHat f1 i).re * (2 : ℝ) ^ i * A2m (k - i)|
      ≤ ∑ i ∈ Finset.range (k + 1), |(bHat f1 i).re * (2 : ℝ) ^ i * A2m (k - i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
          (|(bHat f1 i).re| * (2 : ℝ) ^ i) * (((k : ℝ) + 1) / 2) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (k + 1), |(bHat f1 i).re| * (2 : ℝ) ^ i)
          * (((k : ℝ) + 1) / 2) := by rw [Finset.sum_mul]
    _ ≤ Bhat * (((k : ℝ) + 1) / 2) := by
        apply mul_le_mul_of_nonneg_right hB (by positivity)
    _ = Bhat * ((k : ℝ) + 1) / 2 := by ring

/-- The refined E_1 bound, consuming Theorem 6.1's conclusion. -/
theorem E1k_le_refined (f1 : ℝ) (k : ℕ) (Bhat Gam : ℝ)
    (hB : ∑ i ∈ Finset.range (k + 1), |(bHat f1 i).re| * (2 : ℝ) ^ i ≤ Bhat)
    (h61 : |E1k k - M2k f1 k| ≤ Gam) :
    |E1k k| ≤ Bhat * ((k : ℝ) + 1) / 2 + Gam := by
  have hM := M2k_le f1 k Bhat hB
  have htri : |E1k k| ≤ |E1k k - M2k f1 k| + |M2k f1 k| := by
    have h := abs_sub_abs_le_abs_sub (E1k k) (M2k f1 k)
    have h2 := abs_nonneg (M2k f1 k)
    linarith [h, h2]
  linarith


/-- MANUSCRIPT section 6.2: the refined R(k), with the E_1 term supplied by
Theorem 6.1 rather than by section 3.5's cruder alpha_+ bound.

Replaces alph (3k+4) by Bhat (3k+4)/2 + 3 Gamma, which is sharper whenever
Bhat < 2 alpha_+.  This is the bound behind the manuscript's K0 = 79. -/
noncomputable def RBound2 (Umax Vmax Sstar Bhat Gam : ℝ) (k : ℕ) : ℝ :=
  (Real.log 2 / 4) * ((2 * (k : ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax)
    + Sstar * (2 * DBound k + DBound (k + 1))
    + Bhat * (3 * (k : ℝ) + 4) / 2 + 3 * Gam
    + 3 * (1.45 / (k : ℝ) + 1e-3)

/-- The source bound with the refined E_1 estimate.  This is the route that
makes Theorem 6.1 load-bearing: `h61` is 6.1's conclusion, consumed through
`E1k_le_refined`, which in turn uses `A2m_le`. -/
theorem source_bound_refined (k : ℕ) (hk : 1 ≤ k) (f1 : ℝ)
    (Sstar Bhat Gam Umax Vmax : ℝ)
    (hS : ∀ m : ℕ,
      ∑ i ∈ Finset.range (m + 1), (2 : ℝ) ^ i * |(cCoeff i).re| ≤ Sstar)
    (hB : ∀ m : ℕ,
      ∑ i ∈ Finset.range (m + 1), |(bHat f1 i).re| * (2 : ℝ) ^ i ≤ Bhat)
    (h61 : ∀ m : ℕ, |E1k m - M2k f1 m| ≤ Gam)
    (hUV : |2 * (2 * (k : ℝ) * Uk k - Vk k)
             - (2 * ((k : ℝ) + 1) * Uk (k + 1) - Vk (k + 1))|
           ≤ (2 * (k : ℝ) - 2) * Umax + 2 * Vmax + 4 * Umax)
    (hEexp : ∀ m : ℕ, |Eexpk m| ≤ 1.45 / (k : ℝ) + 1e-3) :
    |2 * Ek k - Ek (k + 1)| ≤ RBound2 Umax Vmax Sstar Bhat Gam k := by
  have hk1 : 1 ≤ k + 1 := by omega
  rw [prop_2_5 k hk, prop_2_5 (k + 1) hk1]
  have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hD := deltaConv_le k Sstar deltaM_abs_le (hS k)
  have hD1 := deltaConv_le (k + 1) Sstar deltaM_abs_le (hS (k + 1))
  have hA := E1k_le_refined f1 k Bhat Gam (hB k) (h61 k)
  have hA1 := E1k_le_refined f1 (k + 1) Bhat Gam (hB (k + 1)) (h61 (k + 1))
  rw [hcast] at hA1
  have hX := hEexp k
  have hX1 := hEexp (k + 1)
  have hq : (0 : ℝ) < Real.log 2 / 4 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  unfold RBound2
  have habs := abs_le.mp hUV
  have hDa := abs_le.mp hD
  have hD1a := abs_le.mp hD1
  have hAa := abs_le.mp hA
  have hA1a := abs_le.mp hA1
  have hXa := abs_le.mp hX
  have hX1a := abs_le.mp hX1
  rw [abs_le]
  constructor <;> nlinarith [habs.1, habs.2, hDa.1, hDa.2, hD1a.1, hD1a.2,
    hAa.1, hAa.2, hA1a.1, hA1a.2, hXa.1, hXa.2, hX1a.1, hX1a.2, hq]

/-- G2deriv1 vanishes at z = 0. -/
theorem G2deriv1_at_zero (f1 : ℝ) : G2deriv1 f1 0 = 0 := by
  unfold G2deriv1
  rw [cBracket_at_zero, mul_zero]
