import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# Alternating and Bisected Lucas Partial Sums

## What This Proves

The parent entry `fibonacci-identities-oq-08` establishes the Lucas telescoping
sum `∑_{i≤n} Lᵢ = L_{n+2} − 1`. This follow-up entry proves the three companion
partial-sum identities requested by that entry's open question, for the Lucas
numbers `L₀ = 2, L₁ = 1, Lₙ₊₂ = Lₙ + Lₙ₊₁`:

* `alt_lucas_sum` — the **alternating sum**
  `∑_{i=0}^{n} (−1)ⁱ Lᵢ = 3 + (−1)ⁿ (L_{n+1} − Lₙ)`, over `ℤ` to carry the sign.
* `lucas_even_sum` — the **even-indexed** (bisected) sum
  `∑_{i=0}^{n} L_{2i} = L_{2n+1} + 1`.
* `lucas_odd_sum` — the **odd-indexed** (bisected) sum
  `∑_{i=0}^{n} L_{2i+1} = L_{2n+2} − 2`.

## The closed forms

**Alternating.** From Binet `Lₙ = φⁿ + ψⁿ` with `φψ = −1` and `1 + φ = φ²`,
the geometric series `∑ (−φ)ⁱ + ∑ (−ψ)ⁱ` telescopes to
`L₂ + (−1)ⁿ L_{n−1} = 3 + (−1)ⁿ L_{n−1}`. Writing `L_{n−1} = L_{n+1} − Lₙ`
gives the subtraction-free `3 + (−1)ⁿ (L_{n+1} − Lₙ)` used here, valid for all
`n` without a negative index.

**Bisections.** Both even- and odd-indexed sums telescope with the two-step
recurrence `L_{k+2} = L_k + L_{k+1}`: the even sum accumulates a `+1` constant
(from `L₁ = 1` shifting the base), the odd sum a `−2` (from `L₀ = 2`).

## How It's Proved

Each identity is a **one-step induction** on `n` using `Finset.sum_range_succ`.
The bisected sums are stated (or reduced to) a subtraction-free `(∑ …) + c = …`
form so `omega` can finish each step from the Lucas recurrence read as a linear
fact over the atoms `L_{2k+1}, L_{2k+2}, L_{2k+3}`. The alternating step keeps
`(−1)ᵏ` as an opaque atom and closes by `ring` after rewriting the recurrence
and `(−1)^{k+1} = −(−1)ᵏ`.

## References

- Parent family: the Lucas telescoping sum `∑_{i≤n} Lᵢ = L_{n+2} − 1`.
- Vajda, *Fibonacci & Lucas Numbers*, bisection and alternating-sum identities.
-/

namespace FibonacciIdentitiesOQ08OQ01

open Nat Finset

/-! ## Definition of the Lucas numbers

Same structural pair recursion as the parent and sibling Lucas entries so this
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

/-- Integer-cast form of the recurrence, convenient for the alternating sum. -/
theorem lucas_add_two_int (n : ℕ) :
    (lucas (n + 2) : ℤ) = (lucas n : ℤ) + (lucas (n + 1) : ℤ) := by
  exact_mod_cast lucas_add_two n

/-! ## The alternating Lucas sum `∑_{i≤n} (−1)ⁱ Lᵢ = 3 + (−1)ⁿ (L_{n+1} − Lₙ)` -/

/-- **Alternating Lucas partial sum.** `∑_{i=0}^{n} (−1)ⁱ Lᵢ =
3 + (−1)ⁿ (L_{n+1} − Lₙ)`, over `ℤ`. One-step induction: the closed form
`g(n) = 3 + (−1)ⁿ(L_{n+1} − Lₙ)` satisfies `g(n+1) = g(n) + (−1)^{n+1} L_{n+1}`
using `L_{n+2} = L_n + L_{n+1}` and `(−1)^{n+1} = −(−1)ⁿ`. -/
theorem alt_lucas_sum (n : ℕ) :
    (∑ i ∈ range (n + 1), (-1 : ℤ) ^ i * (lucas i : ℤ))
      = 3 + (-1) ^ n * ((lucas (n + 1) : ℤ) - (lucas n : ℤ)) := by
  induction n with
  | zero => rw [Finset.sum_range_one]; norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, lucas_add_two_int k, pow_succ]
      ring

/-! ## The even-indexed (bisected) sum `∑_{i≤n} L_{2i} = L_{2n+1} + 1` -/

/-- **Even-indexed Lucas sum.** `∑_{i=0}^{n} L_{2i} = L_{2n+1} + 1`. The new term
`L_{2k+2}` glues to the inductive `L_{2k+1}` via `L_{2k+3} = L_{2k+1} + L_{2k+2}`. -/
theorem lucas_even_sum (n : ℕ) :
    (∑ i ∈ range (n + 1), lucas (2 * i)) = lucas (2 * n + 1) + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hrec : lucas (2 * k + 3) = lucas (2 * k + 1) + lucas (2 * k + 2) :=
        lucas_add_two (2 * k + 1)
      show lucas (2 * k + 1) + 1 + lucas (2 * k + 2) = lucas (2 * k + 3) + 1
      omega

/-! ## The odd-indexed (bisected) sum `∑_{i≤n} L_{2i+1} = L_{2n+2} − 2` -/

/-- **Subtraction-free odd-indexed sum:** `(∑_{i=0}^{n} L_{2i+1}) + 2 = L_{2n+2}`.
The new term `L_{2k+3}` glues to `L_{2k+2}` via `L_{2k+4} = L_{2k+2} + L_{2k+3}`. -/
theorem lucas_odd_sum_add_two (n : ℕ) :
    (∑ i ∈ range (n + 1), lucas (2 * i + 1)) + 2 = lucas (2 * n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hrec : lucas (2 * k + 4) = lucas (2 * k + 2) + lucas (2 * k + 3) :=
        lucas_add_two (2 * k + 2)
      show (∑ i ∈ range (k + 1), lucas (2 * i + 1)) + lucas (2 * k + 3) + 2
          = lucas (2 * k + 4)
      omega

/-- **Odd-indexed Lucas sum:** `∑_{i=0}^{n} L_{2i+1} = L_{2n+2} − 2`
(truncated subtraction over `ℕ`; well-defined since `L_{2n+2} ≥ 2`). -/
theorem lucas_odd_sum (n : ℕ) :
    (∑ i ∈ range (n + 1), lucas (2 * i + 1)) = lucas (2 * n + 2) - 2 := by
  have h := lucas_odd_sum_add_two n
  omega

/-! ## Numerical sanity checks -/

/-- Alternating: `L₀ − L₁ + L₂ − L₃ + L₄ = 2 − 1 + 3 − 4 + 7 = 7`,
matching `3 + (−1)⁴(L₅ − L₄) = 3 + (11 − 7) = 7`. -/
theorem alt_lucas_sum_example :
    (∑ i ∈ range 5, (-1 : ℤ) ^ i * (lucas i : ℤ)) = 7 := by decide

/-- Even-indexed: `L₀ + L₂ + L₄ = 2 + 3 + 7 = 12 = L₅ + 1 = 11 + 1`. -/
theorem lucas_even_sum_example : (∑ i ∈ range 3, lucas (2 * i)) = 12 := by decide

/-- Odd-indexed: `L₁ + L₃ + L₅ = 1 + 4 + 11 = 16 = L₆ − 2 = 18 − 2`. -/
theorem lucas_odd_sum_example : (∑ i ∈ range 3, lucas (2 * i + 1)) = 16 := by decide

end FibonacciIdentitiesOQ08OQ01
