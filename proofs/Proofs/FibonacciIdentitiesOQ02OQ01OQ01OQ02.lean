import Proofs.FibonacciIdentitiesOQ02OQ01OQ01
import Mathlib.Tactic

/-
# The Degree-2 Fibonacci–Lucas Relations

## Open Question OQ-02-OQ-01-OQ-01-OQ-02

The parent (OQ-02-OQ-01-OQ-01) established the *difference* of squares
`Lₙ² − 5·Fₙ² = 4·(−1)ⁿ` (`lucas_sq_sub_five_fib_sq`) and used it to bound
`gcd(Fₙ, Lₙ) ∣ 2`.  Its second open question asks for the **companion
sum-of-squares identity** and the **cross identity**, together forming the full
set of degree-2 relations between the Fibonacci and Lucas sequences:

  Lₙ² + 5·Fₙ² = 2·L₂ₙ                        (sum of squares)            (★)
  Lₙ · Fₙ     =   F₂ₙ                        (cross / doubling)          (✦)

## Why (★) needs no sign

The parent's difference identity `Lₙ² − 5Fₙ² = 4(−1)ⁿ` is *sign governed*: its
right-hand side flips with the parity of `n`.  The **sum** (★), by contrast, is a
pure polynomial identity in `Fₙ` and `Fₙ₊₁` with **no `(−1)ⁿ`** at all.  Writing
`Lₙ = 2Fₙ₊₁ − Fₙ` (`lucas_eq_int`) and expanding the Lucas doubling
`L₂ₙ = 2Fₙ₊₁² + 3Fₙ² − 2FₙFₙ₊₁` (from `fib_two_mul` and `fib_two_mul_add_one`),
both sides of (★) collapse to the same quadratic `4Fₙ₊₁² − 4FₙFₙ₊₁ + 6Fₙ²`.  So
the sum-of-squares relation is the "sign-free half" of the degree-2 algebra, while
the parent's difference carries all of the parity information.

## A bridge back to the parent's sign

Combining (★) with the parent's `Lₙ² = 5Fₙ² + 4(−1)ⁿ` recovers the classical
**Lucas doubling formula** `L₂ₙ = Lₙ² − 2(−1)ⁿ` (`lucas_two_mul_eq_neg_one_pow`),
showing (★) and the parent's difference identity are two faces of one fact.

## Results

1. `fib_two_mul_int` — the integer doubling `F₂ₙ = Fₙ(2Fₙ₊₁ − Fₙ)`, a cast of
   Mathlib's `Nat.fib_two_mul` with the truncated subtraction discharged.
2. `lucas_mul_fib` — the cross identity (✦) `Lₙ · Fₙ = F₂ₙ`.
3. `lucas_two_mul_eq` — the Lucas doubling in `Fₙ, Fₙ₊₁` form
   `L₂ₙ = 2Fₙ₊₁² + 3Fₙ² − 2FₙFₙ₊₁`.
4. `lucas_sq_add_five_fib_sq` — the sum-of-squares identity (★) `Lₙ² + 5Fₙ² = 2L₂ₙ`.
5. `lucas_two_mul_eq_neg_one_pow` — the Lucas doubling `L₂ₙ = Lₙ² − 2(−1)ⁿ`,
   the bridge tying (★) to the parent's sign-carrying difference identity.

## Axioms: 0 | Sorries: 0
-/

namespace FibonacciIdentitiesOQ02OQ01OQ01OQ02

open Nat FibonacciIdentitiesOQ02OQ01OQ01

/-- **Integer Fibonacci doubling.** `F₂ₙ = Fₙ · (2Fₙ₊₁ − Fₙ)` over `ℤ`.  This is
    Mathlib's `Nat.fib_two_mul` with its truncated `ℕ` subtraction lifted to `ℤ`;
    the side condition `Fₙ ≤ 2Fₙ₊₁` holds since `Fₙ ≤ Fₙ₊₁`. -/
theorem fib_two_mul_int (n : ℕ) :
    (fib (2 * n) : ℤ) = fib n * (2 * fib (n + 1) - fib n) := by
  have h1 : fib n ≤ fib (n + 1) := fib_mono (show n ≤ n + 1 by omega)
  have hle : fib n ≤ 2 * fib (n + 1) := by omega
  have h := Nat.fib_two_mul n
  zify [hle] at h
  linarith [h]

/-- **Integer Fibonacci odd doubling.** `F₂ₙ₊₁ = Fₙ₊₁² + Fₙ²` over `ℤ`, a cast of
    Mathlib's `Nat.fib_two_mul_add_one` (which is already subtraction-free). -/
theorem fib_two_mul_add_one_int (n : ℕ) :
    (fib (2 * n + 1) : ℤ) = (fib (n + 1)) ^ 2 + (fib n) ^ 2 := by
  exact_mod_cast Nat.fib_two_mul_add_one n

/-- **Cross identity (✦).** `Lₙ · Fₙ = F₂ₙ`.  Immediate from `Lₙ = 2Fₙ₊₁ − Fₙ`
    and the integer doubling `F₂ₙ = Fₙ(2Fₙ₊₁ − Fₙ)`. -/
theorem lucas_mul_fib (n : ℕ) :
    (lucas n : ℤ) * fib n = fib (2 * n) := by
  rw [lucas_eq_int n, fib_two_mul_int n]; ring

/-- **Lucas doubling in `Fₙ, Fₙ₊₁` form.**
    `L₂ₙ = 2Fₙ₊₁² + 3Fₙ² − 2FₙFₙ₊₁`.  Expand `L₂ₙ = 2F₂ₙ₊₁ − F₂ₙ`
    (`lucas_eq_int`) using the two integer doublings. -/
theorem lucas_two_mul_eq (n : ℕ) :
    (lucas (2 * n) : ℤ)
      = 2 * (fib (n + 1)) ^ 2 + 3 * (fib n) ^ 2 - 2 * fib n * fib (n + 1) := by
  rw [lucas_eq_int (2 * n), fib_two_mul_add_one_int n, fib_two_mul_int n]; ring

/-- **Sum-of-squares identity (★).** `Lₙ² + 5·Fₙ² = 2·L₂ₙ`.  Unlike the parent's
    *difference* `Lₙ² − 5Fₙ² = 4(−1)ⁿ`, the sum carries no sign: both sides reduce
    to `4Fₙ₊₁² − 4FₙFₙ₊₁ + 6Fₙ²`. -/
theorem lucas_sq_add_five_fib_sq (n : ℕ) :
    (lucas n : ℤ) ^ 2 + 5 * (fib n) ^ 2 = 2 * (lucas (2 * n)) := by
  rw [lucas_eq_int n, lucas_two_mul_eq n]; ring

/-- **Lucas doubling formula** `L₂ₙ = Lₙ² − 2(−1)ⁿ`.  The bridge between the
    sign-free sum (★) and the parent's sign-carrying difference `Lₙ² = 5Fₙ² + 4(−1)ⁿ`
    (`lucas_sq_eq`): substituting `5Fₙ² = Lₙ² − 4(−1)ⁿ` into (★) gives
    `2L₂ₙ = 2Lₙ² − 4(−1)ⁿ`. -/
theorem lucas_two_mul_eq_neg_one_pow (n : ℕ) :
    (lucas (2 * n) : ℤ) = (lucas n) ^ 2 - 2 * (-1) ^ n := by
  have h1 := lucas_sq_add_five_fib_sq n
  have h2 := lucas_sq_eq n
  linarith

/-- Sanity check of (★) at `n = 5`: `L₅² + 5·F₅² = 11² + 5·25 = 246 = 2·123 = 2·L₁₀`. -/
example : (lucas 5 : ℤ) ^ 2 + 5 * (fib 5) ^ 2 = 2 * (lucas 10) := by decide

/-- Sanity check of the cross identity (✦) at `n = 6`: `L₆·F₆ = 18·8 = 144 = F₁₂`. -/
example : (lucas 6 : ℤ) * fib 6 = fib 12 := by decide

/-- Sanity check of the Lucas doubling at `n = 5` (odd): `L₁₀ = L₅² − 2(−1)⁵ = 121 + 2 = 123`. -/
example : (lucas 10 : ℤ) = (lucas 5) ^ 2 - 2 * (-1) ^ 5 := by decide

end FibonacciIdentitiesOQ02OQ01OQ01OQ02
