/-!
# Erdős Problem 1073: Composites Dividing Factorial Plus One

Let `A(x)` count the number of composite `u < x` such that `n! + 1 ≡ 0 (mod u)`
for some positive integer `n`. Is `A(x) ≤ x^{o(1)}`?

By Wilson's theorem, every prime `p` divides `(p-1)! + 1`. This problem asks
how many composites share this property. Known composites: 25, 121, 169, 437, ...

*Reference:* [erdosproblems.com/1073](https://www.erdosproblems.com/1073)
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModCast
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Filter

/-! ## Factorial divisibility -/

/-- `DividesFactorialPlusOne u` means there exists `n` with `u ∣ n! + 1`. -/
def DividesFactorialPlusOne (u : ℕ) : Prop :=
    ∃ n : ℕ, u ∣ n ! + 1

/-- The set of composites less than `x` dividing some `n! + 1`. -/
def compositeFactorialSet (x : ℕ) : Set ℕ :=
    { u | u < x ∧ ¬u.Prime ∧ 2 ≤ u ∧ DividesFactorialPlusOne u }

/-- `A(x)` counts composites less than `x` dividing some `n! + 1`. -/
noncomputable def factorialCompositeCount (x : ℕ) : ℕ :=
    (compositeFactorialSet x).ncard

/-! ## Main conjecture -/

/-- Erdős Problem 1073: `A(x) ≤ x^{o(1)}`, i.e., for every `ε > 0`,
`A(x) ≤ x^ε` for large `x`. -/
def ErdosProblem1073 : Prop :=
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
        (factorialCompositeCount x : ℝ) ≤ (x : ℝ) ^ ε

/-! ## Wilson's theorem connection -/

/-- Wilson's theorem: a prime `p` divides `(p-1)! + 1`. -/
axiom wilson_theorem (p : ℕ) (hp : p.Prime) :
    p ∣ (p - 1)! + 1

/-- Every prime satisfies DividesFactorialPlusOne. -/
axiom prime_divides_factorial_plus_one (p : ℕ) (hp : p.Prime) :
    DividesFactorialPlusOne p

/-! ## Known composites -/

/-- 25 divides 4! + 1 = 25. -/
theorem composite_25 : DividesFactorialPlusOne 25 :=
    ⟨4, by norm_num⟩

/-- 121 divides some n! + 1. -/
axiom composite_121 : DividesFactorialPlusOne 121

/-- 169 divides some n! + 1. -/
axiom composite_169 : DividesFactorialPlusOne 169

/-! ## Basic properties -/

/-- 1 divides n! + 1 for all n. -/
theorem one_divides_factorial_plus_one : DividesFactorialPlusOne 1 :=
    ⟨0, one_dvd _⟩

/-- If u divides n! + 1 and d divides u, then d divides n! + 1. -/
theorem dvd_factorial_plus_one_of_dvd {u d : ℕ} (hdu : d ∣ u)
    (hu : DividesFactorialPlusOne u) : DividesFactorialPlusOne d := by
  obtain ⟨n, hn⟩ := hu
  exact ⟨n, dvd_trans hdu hn⟩

/-- A(x) is monotone in x. -/
axiom factorialCompositeCount_mono :
    Monotone factorialCompositeCount
