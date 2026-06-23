/-
  The smallest abundant number is 12.

  A positive integer `n` is *abundant* when the sum of its proper divisors
  exceeds `n` (equivalently `σ(n) > 2n`). Mathlib defines `Nat.Abundant` and
  records `Nat.abundant_twelve : Nat.Abundant 12` (proper divisors of 12 are
  `{1,2,3,4,6}`, summing to `16 > 12`). What Mathlib does *not* record is
  minimality — that no smaller positive integer is abundant.

  This file supplies that missing piece. `not_abundant_below_twelve` is a finite
  divisor-sum computation discharged by `decide` (the bounded `∀ n < 12`
  quantifier is decidable via `Nat.decidableBallLT`, and `Nat.Abundant k` is a
  decidable comparison of concrete sums). Combined with `Nat.abundant_twelve`
  this gives `IsLeast {n | n.Abundant} 12`, i.e. 12 is the least abundant number.

  The proof is axiom-free: `decide` reduces in the kernel, so the result is
  `verified` (no `native_decide`/`Lean.ofReduceBool`).
-/
import Mathlib

namespace AbundantNumberOQ01

/-- 12 is abundant (Mathlib: `Nat.abundant_twelve`); proper divisors `1+2+3+4+6 = 16 > 12`. -/
theorem twelve_abundant : Nat.Abundant 12 := Nat.abundant_twelve

/-- No positive integer below 12 is abundant. Each of the finitely many cases is a
proper-divisor-sum computation; the bounded quantifier is decidable. -/
theorem not_abundant_below_twelve : ∀ n < 12, ¬ Nat.Abundant n := by decide

/-- **The smallest abundant number is 12.** It is abundant, and it is a lower bound
for the set of abundant numbers. -/
theorem smallest_abundant : IsLeast {n : ℕ | n.Abundant} 12 := by
  refine ⟨Nat.abundant_twelve, ?_⟩
  intro n hn
  by_contra h
  push_neg at h
  exact not_abundant_below_twelve n h hn

end AbundantNumberOQ01
