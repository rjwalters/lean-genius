import Mathlib

/-
# Fibonacci numbers at doubled indices as sums and differences of two squares

The fast-doubling identities express a Fibonacci number whose index has been
doubled in terms of two Fibonacci squares.  Mathlib's `Mathlib/Data/Nat/Fib/Basic.lean`
records the *odd* case directly,

* `Nat.fib_two_mul_add_one` : `fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2`,

so an odd-index Fibonacci number is a **sum of two consecutive squares**.  For the
*even* case Mathlib records only the product form

* `Nat.fib_two_mul_add_two` : `fib (2 * n + 2) = fib (n + 1) * (2 * fib n + fib (n + 1))`,

and **not** the dual "difference of two squares" reading

  `fib (2 * n + 2) = fib (n + 2) ^ 2 - fib n ^ 2`,

which is the even-index companion of the odd-index sum-of-squares identity and is
absent from both Mathlib and this gallery.  This entry supplies it, in an
`ℕ`-additive form `fib (2 * n + 2) + fib n ^ 2 = fib (n + 2) ^ 2` and an `ℤ`-subtractive
form, records the odd case for symmetry, and packages both as existential
"sum / difference of two squares" statements.

The even identity is elementary: combine `Nat.fib_two_mul_add_two` with the
recurrence `fib (n + 2) = fib n + fib (n + 1)` and expand the square.  The cross term
`2 * fib n * fib (n + 1)` of `(fib n + fib (n + 1)) ^ 2` is exactly the difference
between the product form `fib (n + 1) * (2 * fib n + fib (n + 1))` and `fib n ^ 2`,
so the whole thing closes by `ring`.
-/

namespace FibonacciIdentitiesOQ03

/-- **Odd-index Fibonacci numbers are sums of two consecutive squares.**
`fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2` — this is Mathlib's
`Nat.fib_two_mul_add_one`, recorded here as the odd half of the
sum / difference-of-squares pair. -/
theorem fib_odd_sq_add_sq (n : ℕ) :
    Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 :=
  Nat.fib_two_mul_add_one n

/-- **Even-index Fibonacci numbers are differences of two squares** (additive `ℕ`
form). `fib (2 * n + 2) + fib n ^ 2 = fib (n + 2) ^ 2`, equivalently
`fib (2 * n + 2) = fib (n + 2) ^ 2 - fib n ^ 2`.  This is the even-index companion
of `fib_odd_sq_add_sq` and is absent from Mathlib, whose even-doubling lemma
`Nat.fib_two_mul_add_two` is stated in product form. -/
theorem fib_even_add_sq_eq_sq (n : ℕ) :
    Nat.fib (2 * n + 2) + Nat.fib n ^ 2 = Nat.fib (n + 2) ^ 2 := by
  rw [Nat.fib_two_mul_add_two, Nat.fib_add_two]
  ring

/-- **Even-index difference of two squares**, integer subtractive form.
`fib (2 * n + 2) = fib (n + 2) ^ 2 - fib n ^ 2` over `ℤ`, making the "difference of
two squares" literal (no truncated subtraction). -/
theorem fib_even_sq_sub_sq (n : ℕ) :
    (Nat.fib (2 * n + 2) : ℤ) = (Nat.fib (n + 2) : ℤ) ^ 2 - (Nat.fib n : ℤ) ^ 2 := by
  have h : (Nat.fib (2 * n + 2) : ℤ) + (Nat.fib n : ℤ) ^ 2 = (Nat.fib (n + 2) : ℤ) ^ 2 := by
    exact_mod_cast fib_even_add_sq_eq_sq n
  linarith

/-- Existential reading of the odd case: every odd-index Fibonacci number is a sum
of two squares (indeed of two consecutive Fibonacci squares). -/
theorem fib_odd_isSumSq (n : ℕ) :
    ∃ a b : ℕ, Nat.fib (2 * n + 1) = a ^ 2 + b ^ 2 :=
  ⟨Nat.fib (n + 1), Nat.fib n, fib_odd_sq_add_sq n⟩

/-- Existential reading of the even case: every even-index Fibonacci number
`fib (2 * n + 2)` is a difference of two squares `a ^ 2 - b ^ 2`
(with `a = fib (n + 2)`, `b = fib n`). -/
theorem fib_even_isDiffSq (n : ℕ) :
    ∃ a b : ℕ, Nat.fib (2 * n + 2) + b ^ 2 = a ^ 2 :=
  ⟨Nat.fib (n + 2), Nat.fib n, fib_even_add_sq_eq_sq n⟩

end FibonacciIdentitiesOQ03
