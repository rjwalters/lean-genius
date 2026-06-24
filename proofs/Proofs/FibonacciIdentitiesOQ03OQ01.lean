import Mathlib

/-
# Fibonacci numbers at index `4n+3` as a sum of two squares (iterated doubling)

The parent entry `FibonacciIdentitiesOQ03` records the two halves of the
fast-doubling identities:

* `Nat.fib_two_mul_add_one`  : `fib (2n+1) = fib (n+1)² + fib n²`   (odd → sum of two squares)
* `Nat.fib_two_mul_add_two`  : `fib (2n+2) = fib (n+1)·(2·fib n + fib (n+1))` (even, product form)

This entry **iterates the doubling once more**.  Writing `4n+3 = 2·(2n+1)+1`,
the odd-doubling identity applied at index `2n+1` gives the *outer* layer

  `fib (4n+3) = fib (2n+2)² + fib (2n+1)²`,

an honest sum of two squares.  Substituting the *inner* layer — the two parent
identities for `fib (2n+1)` and `fib (2n+2)` — re-expresses `fib (4n+3)` entirely
in terms of the two consecutive base values `a = fib n`, `b = fib (n+1)`:

  `fib (4n+3) = (b·(2a+b))² + (b²+a²)²`.

This is a genuine sum-of-two-squares decomposition with *explicit* low-index
terms, the content the open question asks for.  Everything is over `ℕ` with no
truncated subtraction, so the existential "sum of two squares" reading holds
without casting to `ℤ`.

The proof is elementary: two applications of Mathlib's `fib_two_mul_add_one`
(one to peel the outer layer, one for the inner odd term), one application of
`fib_two_mul_add_two` for the inner even term, and `ring` to expand.
-/

namespace FibonacciIdentitiesOQ03OQ01

/-- **Outer doubling layer.** Applying the odd fast-doubling identity at index
`2n+1` expresses `fib (4n+3)` as the sum of the two squares `fib (2n+2)²` and
`fib (2n+1)²`.  This is the `4n+3` companion of `Nat.fib_two_mul_add_one`. -/
theorem fib_four_mul_add_three (n : ℕ) :
    Nat.fib (4 * n + 3) = Nat.fib (2 * n + 2) ^ 2 + Nat.fib (2 * n + 1) ^ 2 := by
  have h : Nat.fib (2 * (2 * n + 1) + 1)
      = Nat.fib ((2 * n + 1) + 1) ^ 2 + Nat.fib (2 * n + 1) ^ 2 :=
    Nat.fib_two_mul_add_one (2 * n + 1)
  have hidx : 2 * (2 * n + 1) + 1 = 4 * n + 3 := by ring
  have hidx2 : (2 * n + 1) + 1 = 2 * n + 2 := by ring
  rw [hidx, hidx2] at h
  exact h

/-- **Iterated form.** Substituting the parent doubling identities for the inner
`fib (2n+1)` and `fib (2n+2)` re-expresses `fib (4n+3)` as a sum of two squares
in the two consecutive base values `fib n` and `fib (n+1)` alone:

`fib (4n+3) = (fib (n+1)·(2·fib n + fib (n+1)))² + (fib (n+1)² + fib n²)²`. -/
theorem fib_four_mul_add_three_iterated (n : ℕ) :
    Nat.fib (4 * n + 3)
      = (Nat.fib (n + 1) * (2 * Nat.fib n + Nat.fib (n + 1))) ^ 2
        + (Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2) ^ 2 := by
  rw [fib_four_mul_add_three, Nat.fib_two_mul_add_two, Nat.fib_two_mul_add_one]

/-- **Existential reading.** Every Fibonacci number at index `4n+3` is a sum of
two squares, exhibited with explicit low-index witnesses. -/
theorem fib_four_mul_add_three_isSumSq (n : ℕ) :
    ∃ a b : ℕ, Nat.fib (4 * n + 3) = a ^ 2 + b ^ 2 :=
  ⟨Nat.fib (n + 1) * (2 * Nat.fib n + Nat.fib (n + 1)),
   Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2,
   fib_four_mul_add_three_iterated n⟩

/-- **Integer form** of the iterated decomposition, making the two squares literal
over `ℤ` (the `ℕ` statement already involves no subtraction, but the `ℤ` version
is convenient for downstream algebra). -/
theorem fib_four_mul_add_three_iterated_int (n : ℕ) :
    (Nat.fib (4 * n + 3) : ℤ)
      = ((Nat.fib (n + 1) : ℤ) * (2 * Nat.fib n + Nat.fib (n + 1))) ^ 2
        + ((Nat.fib (n + 1) : ℤ) ^ 2 + (Nat.fib n : ℤ) ^ 2) ^ 2 := by
  exact_mod_cast fib_four_mul_add_three_iterated n

/-- Sanity checks against directly computed Fibonacci values. -/
example : Nat.fib 3 = 2 := by decide          -- n = 0 : 4·0+3 = 3
example : Nat.fib 7 = 13 := by decide          -- n = 1 : 4·1+3 = 7
example : Nat.fib 11 = 89 := by decide         -- n = 2 : 4·2+3 = 11

end FibonacciIdentitiesOQ03OQ01
