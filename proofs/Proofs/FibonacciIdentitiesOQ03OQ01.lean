import Mathlib

/-
# Fibonacci OQ-03 / OQ-01: the doubling identity F_{2m} = F_m · L_m via Lucas numbers

The parent (`FibonacciIdentitiesOQ03`) shows that an even-index Fibonacci number is a
**difference of two squares**,

* `fib (2*n+2) = fib (n+2)^2 - fib n^2`   (`fib_even_sq_sub_sq`).

A difference of two squares always factors: `a^2 - b^2 = (a - b)(a + b)`.  Here
`a = fib (n+2)`, `b = fib n`, and the factors are

* `a - b = fib (n+2) - fib n = fib (n+1)`   (the Fibonacci recurrence), and
* `a + b = fib (n+2) + fib n`,

the second of which is exactly the **Lucas number** `L_{n+1}`.  So the parent's difference
of squares factors as

  `fib (2*n+2) = fib (n+1) · L_{n+1}`,

i.e. the classical doubling identity `F_{2m} = F_m · L_m`.

Mathlib has Fibonacci numbers (`Nat.fib`) but **no Lucas sequence**.  This entry therefore
introduces `lucas`, proves the Fibonacci–Lucas bridge `L_{n+1} = F_n + F_{n+2}`, and uses it
to package the doubling identity `F_{2m} = F_m · L_m` for all `m` — exhibiting the parent's
difference of squares as a genuine product factorization.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ03OQ01

open Nat

/-- **Lucas numbers** `L : ℕ → ℕ`, the companion sequence to the Fibonacci numbers:
`L 0 = 2`, `L 1 = 1`, and `L (n+2) = L n + L (n+1)`.  Mathlib has `Nat.fib` but no Lucas
sequence, so we define it here. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The Lucas recurrence `L (n+2) = L n + L (n+1)`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- **Fibonacci–Lucas bridge.** `L_{n+1} = F_n + F_{n+2}`.  (Equivalently the more familiar
`L_n = F_{n-1} + F_{n+1}`, stated in a shift that avoids truncated subtraction.) -/
theorem lucas_succ_eq_fib (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    -- L_{n+3} = L_{n+1} + L_{n+2}; apply the bridge at n and n+1, then expand all fibs
    have e1 : n + 2 + 1 = (n + 1) + 2 := by ring
    rw [e1, lucas_add_two, ih1, ih2]
    simp only [Nat.fib_add_two]
    ring

/-- **The doubling identity `F_{2m} = F_m · L_m`.**  This factors the parent's difference of
squares `fib (2*n+2) = fib (n+2)^2 - fib n^2`: the factors `fib (n+2) - fib n = fib (n+1)`
and `fib (n+2) + fib n = L_{n+1}` give `fib (2m) = fib m · L_m`. -/
theorem fib_two_mul_eq (m : ℕ) : Nat.fib (2 * m) = Nat.fib m * lucas m := by
  cases m with
  | zero => simp
  | succ n =>
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring, Nat.fib_two_mul_add_two,
      lucas_succ_eq_fib, Nat.fib_add_two]
    ring

/-- **The parent's difference of squares as an explicit product.**  Reading
`fib (2*n+2) = fib (n+2)^2 - fib n^2` through `a^2 - b^2 = (a-b)(a+b)` gives the factorization
`fib (2*n+2) = fib (n+1) * (fib (n+2) + fib n)`, whose second factor is `L_{n+1}`. -/
theorem fib_even_factorization (n : ℕ) :
    Nat.fib (2 * n + 2) = Nat.fib (n + 1) * (Nat.fib (n + 2) + Nat.fib n) := by
  have h := fib_two_mul_eq (n + 1)
  rwa [show 2 * (n + 1) = 2 * n + 2 from by ring, lucas_succ_eq_fib,
    Nat.add_comm (Nat.fib n) (Nat.fib (n + 2))] at h

/-- Existential packaging: every even-index Fibonacci number `fib (2m)` is a product of a
Fibonacci number and the corresponding Lucas number. -/
theorem fib_even_isProd (m : ℕ) : ∃ a b : ℕ, Nat.fib (2 * m) = a * b :=
  ⟨Nat.fib m, lucas m, fib_two_mul_eq m⟩

/-- Sanity check on small values: `F_{2·5} = F_10 = 55 = 5 · 11 = F_5 · L_5`. -/
example : Nat.fib (2 * 5) = Nat.fib 5 * lucas 5 := fib_two_mul_eq 5

end FibonacciIdentitiesOQ03OQ01

/-
## Summary

* `lucas` — the Lucas number sequence (absent from Mathlib).
* `lucas_succ_eq_fib` — the Fibonacci–Lucas bridge `L_{n+1} = F_n + F_{n+2}`.
* `fib_two_mul_eq` — the doubling identity `F_{2m} = F_m · L_m`, for all `m`.
* `fib_even_factorization` — the parent's difference of squares `fib (n+2)^2 - fib n^2` as the
  explicit product `fib (n+1) · (fib (n+2) + fib n)`.

So the even-index "difference of two squares" from the parent entry is, concretely, the
Fibonacci–Lucas doubling product.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
