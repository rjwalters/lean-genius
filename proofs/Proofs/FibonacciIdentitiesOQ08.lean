import Mathlib

/-!
# Lucas-number summation identities

Mathlib records the Fibonacci sequence `Nat.fib` together with a rich collection of
pointwise identities (`Nat.fib_add_two`, `Nat.fib_add`, `Nat.fib_two_mul`, …), but it
carries **no Lucas sequence** at all. The Lucas numbers `Lₙ` obey the same recurrence
as the Fibonacci numbers, `Lₙ₊₂ = Lₙ₊₁ + Lₙ`, but start from the seed `L₀ = 2`,
`L₁ = 1`; they are the companion sequence to `Fₙ` and satisfy `Lₙ = Fₙ₋₁ + Fₙ₊₁`.

This entry (following the parent `FibonacciIdentities` summation template) builds the
Lucas sequence from scratch and proves the classical summation and mixed identities,
each a fully self-contained induction — no axioms, no `native_decide`:

* `lucas_add_fib` — the **Lucas–Fibonacci bridge** `Lₙ + Fₙ = 2·Fₙ₊₁`, equivalently
  `Lₙ = 2Fₙ₊₁ − Fₙ = Fₙ₊₁ + Fₙ₋₁`. Proved by two-step induction on the shared
  recurrence; it is the sole link we need between the two sequences.

* `lucas_sum` — the **partial sums of the Lucas numbers**:
  `(L₀ + L₁ + ⋯ + Lₙ) + 1 = Lₙ₊₂` (stated additively to stay inside `ℕ`). The exact
  analogue of the Fibonacci partial-sum law `∑ Fᵢ = Fₙ₊₂ − 1`.

* `fib_mul_lucas` — the **doubling identity** `Fₙ · Lₙ = F₂ₙ`. This is Mathlib's
  `Nat.fib_two_mul` reread through the bridge: `2Fₙ₊₁ − Fₙ = Lₙ`.

* `fib_mul_lucas_sum` — the **mixed partial sum** `(∑ᵢ Fᵢ·Lᵢ) + 1 = F₂ₙ₊₁`, obtained
  by summing the doubling identity `Fᵢ·Lᵢ = F₂ᵢ` and telescoping through the Fibonacci
  recurrence.

The only Fibonacci facts used are the recurrence `Nat.fib_add_two` and the doubling
formula `Nat.fib_two_mul`; everything else is `Finset.sum_range_succ`, the Lucas
recurrence, and `omega`.

No axioms, no sorries.
-/

namespace FibonacciIdentitiesOQ08

open Finset

/-- The **Lucas numbers** `Lₙ`: the same recurrence as the Fibonacci numbers,
`Lₙ₊₂ = Lₙ₊₁ + Lₙ`, but with the seed `L₀ = 2`, `L₁ = 1`. Mathlib has `Nat.fib`
but no Lucas sequence, so we define it here. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- Defining recurrence of the Lucas numbers: `Lₙ₊₂ = Lₙ₊₁ + Lₙ`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- **Lucas–Fibonacci bridge.** `Lₙ + Fₙ = 2·Fₙ₊₁`, equivalently `Lₙ = Fₙ₊₁ + Fₙ₋₁`.
Both sequences obey the same recurrence, so the identity propagates by two-step
induction from the two seed values. -/
theorem lucas_add_fib (n : ℕ) : lucas n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    have hf2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have hf3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) :=
      Nat.fib_add_two (n := n + 1)
    have ih2' : lucas (n + 1) + Nat.fib (n + 1) = 2 * Nat.fib (n + 2) := ih2
    have hl : lucas (n + 2) = lucas (n + 1) + lucas n := lucas_add_two n
    show lucas (n + 2) + Nat.fib (n + 2) = 2 * Nat.fib (n + 3)
    omega

/-- **Sum of the Lucas numbers** (additive form, to stay in `ℕ`):
`(L₀ + L₁ + ⋯ + Lₙ) + 1 = Lₙ₊₂`. The Lucas analogue of `∑ Fᵢ = Fₙ₊₂ − 1`. -/
theorem lucas_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), lucas i) + 1 = lucas (n + 2) := by
  induction n with
  | zero => simp [lucas]
  | succ k ih =>
    rw [Finset.sum_range_succ, lucas_add_two (k + 1)]
    have hy : lucas (k + 1 + 1) = lucas (k + 2) := rfl
    omega

/-- **Doubling identity** `Fₙ · Lₙ = F₂ₙ`. This is Mathlib's `Nat.fib_two_mul`
(`F₂ₙ = Fₙ · (2Fₙ₊₁ − Fₙ)`) read through the bridge `Lₙ = 2Fₙ₊₁ − Fₙ`. -/
theorem fib_mul_lucas (n : ℕ) : Nat.fib n * lucas n = Nat.fib (2 * n) := by
  have h := lucas_add_fib n
  rw [Nat.fib_two_mul]
  have hl : lucas n = 2 * Nat.fib (n + 1) - Nat.fib n := by omega
  rw [hl]

/-- **Mixed partial sum** `(F₀L₀ + F₁L₁ + ⋯ + FₙLₙ) + 1 = F₂ₙ₊₁`. Each term is an
even-indexed Fibonacci number (`Fᵢ·Lᵢ = F₂ᵢ`), and the sum telescopes through the
Fibonacci recurrence. -/
theorem fib_mul_lucas_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i * lucas i) + 1 = Nat.fib (2 * n + 1) := by
  induction n with
  | zero => simp [lucas]
  | succ k ih =>
    rw [Finset.sum_range_succ, fib_mul_lucas]
    have e : Nat.fib (2 * (k + 1) + 1) = Nat.fib (2 * k + 1) + Nat.fib (2 * (k + 1)) := by
      have h := Nat.fib_add_two (n := 2 * k + 1)
      have h2 : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
      have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [h2, h1] at h
      omega
    omega

end FibonacciIdentitiesOQ08
