import Mathlib

/-!
# Sum of Divisors OQ-05: the abundancy index σ(n)/n is multiplicative

The **abundancy index** of `n` is the rational number `abundancy n = σ₁(n) / n`, where
`σ₁(n)` is the sum of the divisors of `n`. It measures how "divisor-rich" `n` is:
`< 2` deficient, `= 2` perfect, `> 2` abundant.

The `SumOfDivisors` gallery entry proves that the divisor-sum function `σ₁` itself is
multiplicative (`σ₁(mn) = σ₁(m)·σ₁(n)` for coprime `m, n`) and characterizes perfect
numbers by `abundancy n = 2`, but it does **not** record that the *rational quotient*
`σ₁(n)/n` is multiplicative. This entry supplies that:

* `abundancy_mul_of_coprime` : `abundancy (m·n) = abundancy m · abundancy n` for coprime
  positive `m, n` — the abundancy index is a multiplicative function.

Two consequences are read off:

* `one_lt_abundancy` : `abundancy n > 1` for every `n ≥ 2` (since `σ₁(n) > n`), and
* `abundant_of_perfect_mul_coprime` : a positive coprime multiple of a perfect number is
  **abundant** — if `abundancy m = 2` and `n ≥ 2` is coprime to `m`, then
  `abundancy (m·n) > 2`. (This is why, e.g., `2·k` is abundant for odd `k > 1` once one
  factor is perfect — the multiplicativity transports "perfect" past a coprime factor.)

Self-contained: `abundancy` is defined here over `ℚ` from Mathlib's `ArithmeticFunction.sigma`,
and no `native_decide` is used, so the file is genuinely axiom-free.

No axioms, no sorries.
-/

namespace SumOfDivisorsOQ05

open ArithmeticFunction

/-- The abundancy index `σ₁(n)/n` as a rational number. -/
noncomputable def abundancy (n : ℕ) : ℚ := (sigma 1 n : ℚ) / (n : ℚ)

@[simp] theorem abundancy_one : abundancy 1 = 1 := by
  simp [abundancy]

/-- **The abundancy index is multiplicative.** For coprime positive `m, n`,
`abundancy (m·n) = abundancy m · abundancy n`. This is the rational-quotient upgrade of
the multiplicativity of `σ₁` itself. -/
theorem abundancy_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : Nat.Coprime m n) :
    abundancy (m * n) = abundancy m * abundancy n := by
  have hmn : sigma 1 (m * n) = sigma 1 m * sigma 1 n :=
    isMultiplicative_sigma.map_mul_of_coprime h
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold abundancy
  rw [hmn]
  push_cast
  field_simp

/-- The divisor sum strictly exceeds `n` once `n ≥ 2`: both `1` and `n` are distinct
divisors, so `σ₁(n) ≥ 1 + n > n`. -/
theorem self_lt_sigma_one {n : ℕ} (hn : 2 ≤ n) : n < sigma 1 n := by
  have hn0 : n ≠ 0 := by omega
  rw [sigma_one_apply]
  have hsub : ({n} : Finset ℕ) ⊆ n.divisors := by
    simp [Finset.singleton_subset_iff, Nat.mem_divisors, hn0]
  have h1mem : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have h1not : (1 : ℕ) ∉ ({n} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  calc n = ∑ d ∈ ({n} : Finset ℕ), d := by simp
    _ < ∑ d ∈ n.divisors, d :=
        Finset.sum_lt_sum_of_subset hsub h1mem h1not (by norm_num)
          (fun j _ _ => Nat.zero_le j)

/-- **Every `n ≥ 2` has abundancy `> 1`** (it is at least "deficient-strict"):
`abundancy n = σ₁(n)/n > 1` because `σ₁(n) > n`. -/
theorem one_lt_abundancy {n : ℕ} (hn : 2 ≤ n) : 1 < abundancy n := by
  have hpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  rw [abundancy, lt_div_iff₀ hpos, one_mul]
  exact_mod_cast self_lt_sigma_one hn

/-- **A coprime multiple of a perfect number is abundant.** If `m` is perfect
(`abundancy m = 2`) and `n ≥ 2` is coprime to `m`, then `abundancy (m·n) > 2`, i.e. `m·n`
is abundant. Multiplicativity pushes the perfect value `2` past the coprime factor `n`,
whose abundancy exceeds `1`. -/
theorem abundant_of_perfect_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (h : Nat.Coprime m n) (hperf : abundancy m = 2) :
    2 < abundancy (m * n) := by
  rw [abundancy_mul_of_coprime hm (by omega) h, hperf]
  have hn1 : 1 < abundancy n := one_lt_abundancy hn
  linarith

end SumOfDivisorsOQ05
