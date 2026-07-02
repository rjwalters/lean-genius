import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# Lucas-number Partial-Sum Identities

## What This Proves

The parent gallery family formalizes the **Fibonacci telescoping sum**
`∑_{i≤n} Fᵢ = F_{n+2} − 1`. This entry establishes the exact **Lucas-number**
analogues, for the companion sequence `L₀ = 2, L₁ = 1, Lₙ₊₂ = Lₙ + Lₙ₊₁`:

* `lucas_sum`      —  `∑_{i=0}^{n} Lᵢ = L_{n+2} − 1`.
* `fib_mul_lucas_sum` —  `∑_{i=0}^{n} Fᵢ·Lᵢ = F_{2n+1} − 1`, the *mixed*
  Fibonacci–Lucas telescoping sum.

Along the way we prove the fundamental **product identity**
`Fₙ · Lₙ = F_{2n}` (`fib_mul_lucas`), the multiplicative bridge that turns the
mixed sum into a sum of even-indexed Fibonacci numbers.

## The telescoped constant

Both sums telescope with correction `−1`. For the Lucas sum,
`Lᵢ = L_{i+2} − L_{i+1}`, so `∑_{i=0}^{n} Lᵢ = L_{n+2} − L₁ = L_{n+2} − 1`
(the constant is `L₁ = 1`, exactly as `F₁ = 1` gives the `−1` in the Fibonacci
sum, despite `L₀ = 2`). We record the subtraction-free form
`lucas_sum_add_one` first, from which the truncated-subtraction statement
follows by `omega`.

## How It's Proved

Both partial sums close under a **one-step induction** using
`Finset.sum_range_succ`, stated in the subtraction-free `(∑ …) + c = …` form so
`omega` can finish each step from the defining recurrence.

The mixed sum needs the product identity `Fₙ·Lₙ = F_{2n}`. We prove the
subtraction-free bridge `2·Fₙ₊₁ = Lₙ + Fₙ` by two-step induction, giving
`Lₙ = 2·Fₙ₊₁ − Fₙ` over `ℕ`; substituting into Mathlib's
`Nat.fib_two_mul` (`F_{2n} = Fₙ·(2·Fₙ₊₁ − Fₙ)`) yields `Fₙ·Lₙ = F_{2n}`
immediately.

## References

- The Fibonacci telescoping sum `∑_{i≤n} Fᵢ = F_{n+2} − 1` (parent family).
- Lucas numbers and the identity `Fₙ·Lₙ = F_{2n}` (Vajda, *Fibonacci & Lucas
  Numbers*, identities (17a), (23)).
-/

namespace FibonacciIdentitiesOQ08

open Nat Finset

/-! ## Definition of the Lucas numbers

We use the same structural pair recursion as the sibling Lucas entries so this
file is self-contained; `lucas` reduces by `rfl`. -/

/-- The pair `(Lₙ, Lₙ₊₁)`. -/
def lucasPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | n + 1 => ((lucasPair n).2, (lucasPair n).1 + (lucasPair n).2)

/-- The Lucas numbers `Lₙ`: `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ + Lₙ₊₁`. -/
def lucas (n : ℕ) : ℕ := (lucasPair n).1

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining recurrence `Lₙ₊₂ = Lₙ + Lₙ₊₁`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-! ## The Lucas telescoping sum `∑_{i≤n} Lᵢ = L_{n+2} − 1` -/

/-- **Subtraction-free Lucas partial sum:** `(∑_{i=0}^{n} Lᵢ) + 1 = L_{n+2}`.
One-step induction: the new term `L_{k+1}` combines with the inductive
`L_{k+2}` via `L_{k+3} = L_{k+1} + L_{k+2}`. -/
theorem lucas_sum_add_one (n : ℕ) :
    (∑ i ∈ range (n + 1), lucas i) + 1 = lucas (n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hr : lucas (k + 3) = lucas (k + 1) + lucas (k + 2) := lucas_add_two (k + 1)
      -- goal: (∑_{range (k+1)} Lᵢ) + L_{k+1} + 1 = L_{k+3}
      show (∑ i ∈ range (k + 1), lucas i) + lucas (k + 1) + 1 = lucas (k + 3)
      omega

/-- **Lucas telescoping sum:** `∑_{i=0}^{n} Lᵢ = L_{n+2} − 1` (truncated
subtraction over `ℕ`; well-defined since `L_{n+2} ≥ 1`). -/
theorem lucas_sum (n : ℕ) :
    (∑ i ∈ range (n + 1), lucas i) = lucas (n + 2) - 1 := by
  have h := lucas_sum_add_one n
  omega

/-! ## The product identity `Fₙ · Lₙ = F_{2n}` -/

/-- The subtraction-free Fibonacci–Lucas bridge `2·Fₙ₊₁ = Lₙ + Fₙ`,
by two-step induction. -/
theorem two_mul_fib_succ (n : ℕ) : 2 * fib (n + 1) = lucas n + fib n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      have h1 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      have h2 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
      have h3 : lucas (n + 2) = lucas n + lucas (n + 1) := lucas_add_two n
      have e1 : 2 * fib (n + 1) = lucas n + fib n := ih1
      have e2 : 2 * fib (n + 2) = lucas (n + 1) + fib (n + 1) := ih2
      show 2 * fib (n + 3) = lucas (n + 2) + fib (n + 2)
      omega

/-- **The product identity `Fₙ · Lₙ = F_{2n}`.** Substitute the bridge
`Lₙ = 2·Fₙ₊₁ − Fₙ` into `Nat.fib_two_mul`. -/
theorem fib_mul_lucas (n : ℕ) : fib n * lucas n = fib (2 * n) := by
  have hb := two_mul_fib_succ n                         -- 2·F_{n+1} = Lₙ + Fₙ
  have hl : lucas n = 2 * fib (n + 1) - fib n := by omega
  rw [fib_two_mul, hl]

/-! ## The mixed Fibonacci–Lucas telescoping sum `∑_{i≤n} Fᵢ·Lᵢ = F_{2n+1} − 1` -/

/-- **Subtraction-free mixed sum:** `(∑_{i=0}^{n} Fᵢ·Lᵢ) + 1 = F_{2n+1}`.
Using `Fᵢ·Lᵢ = F_{2i}`, this is the sum of even-indexed Fibonacci numbers;
the induction step glues `F_{2k+1} + F_{2k+2} = F_{2k+3}`. -/
theorem fib_mul_lucas_sum_add_one (n : ℕ) :
    (∑ i ∈ range (n + 1), fib i * lucas i) + 1 = fib (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
      rw [Finset.sum_range_succ]
      -- normalise the new term to `F_{2k+2}` (defeq `F_{2(k+1)}`)
      have hp : fib (k + 1) * lucas (k + 1) = fib (2 * k + 2) := by
        rw [show 2 * k + 2 = 2 * (k + 1) from by ring]; exact fib_mul_lucas (k + 1)
      -- `F_{2k+3} = F_{2k+1} + F_{2k+2}` (defeq of `fib_add_two` at `2k+1`)
      have hf : fib (2 * k + 3) = fib (2 * k + 1) + fib (2 * k + 2) :=
        fib_add_two (n := 2 * k + 1)
      -- goal: (∑_{range (k+1)} Fᵢ·Lᵢ) + F_{k+1}·L_{k+1} + 1 = F_{2(k+1)+1}
      show (∑ i ∈ range (k + 1), fib i * lucas i) + fib (k + 1) * lucas (k + 1) + 1
          = fib (2 * k + 3)
      omega

/-- **Mixed Fibonacci–Lucas telescoping sum:** `∑_{i=0}^{n} Fᵢ·Lᵢ = F_{2n+1} − 1`
(truncated subtraction; well-defined since `F_{2n+1} ≥ 1`). -/
theorem fib_mul_lucas_sum (n : ℕ) :
    (∑ i ∈ range (n + 1), fib i * lucas i) = fib (2 * n + 1) - 1 := by
  have h := fib_mul_lucas_sum_add_one n
  omega

/-! ## Numerical sanity checks -/

/-- `L₀ + L₁ + L₂ + L₃ = 2 + 1 + 3 + 4 = 10 = L₅ − 1 = 11 − 1`. -/
theorem lucas_sum_example : (∑ i ∈ range 4, lucas i) = 10 := by decide

/-- `F₀L₀ + … + F₃L₃ = 0 + 1 + 3 + 8 = 12 = F₇ − 1 = 13 − 1`. -/
theorem fib_mul_lucas_sum_example : (∑ i ∈ range 4, fib i * lucas i) = 12 := by decide

/-- The product identity on a sample index: `F₆·L₆ = 8·18 = 144 = F₁₂`. -/
theorem fib_mul_lucas_example : fib 6 * lucas 6 = fib 12 := by decide

end FibonacciIdentitiesOQ08
