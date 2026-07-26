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
