import Mathlib

/-
# Partial Sums of the Lucas Numbers: `∑_{k=1}^{n} L_k = L_{n+2} − 3`

## Open Question OQ-01 (gallery gap)

The Lucas numbers `2, 1, 3, 4, 7, 11, 18, …` obey the same second-order recurrence as
the Fibonacci numbers, `L_{n+2} = L_n + L_{n+1}`, with the alternative initial data
`L_0 = 2`, `L_1 = 1`.  Their partial sums satisfy the telescoping identity

  ∑_{k=1}^{n} L_k = L_{n+2} − 3 .

For example `L_1 + L_2 + L_3 = 1 + 3 + 4 = 8 = L_5 − 3 = 11 − 3`.

This is the Lucas analogue of the Fibonacci telescoping sum `∑_{k=1}^{n} F_k = F_{n+2} − 1`
already in the gallery.  Mathlib provides `Nat.fib` but no packaged Lucas-number
partial-sum lemma, so this is a clean, self-contained gallery gap.

## What is proved here

1. `lucas_sum_add_three` — the subtraction-free form
        (∑_{k<n} L_{k+1}) + 3 = L_{n+2},
   proved by induction on `n` directly from the recurrence; this is the exact statement
   the telescoping argument produces and avoids all `ℕ`-subtraction edge cases.

2. `lucas_sum` — the headline identity `∑_{k=1}^{n} L_k = L_{n+2} − 3` in `ℕ`,
   read off from (1) (legitimate because `L_{n+2} ≥ 3`).

3. `lucas_succ_eq_fib_add_fib` — the bridge `L_{n+1} = F_n + F_{n+2}` to Mathlib's
   `Nat.fib`, validating that this self-contained `lucas` agrees with the standard
   Fibonacci-based Lucas numbers.  (Same two-step induction used in
   `FibonacciIdentitiesOQ03OQ03`.)

The 1-indexed sum `∑_{k=1}^{n} L_k` is encoded as `∑ k ∈ Finset.range n, lucas (k+1)`,
so the summand runs over `L_1, …, L_n`.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSumOQ01

open Finset

/-- The Lucas numbers `2, 1, 3, 4, 7, 11, …` — the Fibonacci recurrence with the
alternative initial data `L_0 = 2`, `L_1 = 1`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining Lucas recurrence `L_{n+2} = L_n + L_{n+1}`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- **Telescoping partial sum (subtraction-free).**
`(∑_{k=1}^{n} L_k) + 3 = L_{n+2}`.

Proof by induction on `n`.  The base case is `0 + 3 = L_2 = 3`.  In the step,
`Finset.sum_range_succ` peels off the new term `L_{n+1}`, and the Lucas recurrence
`L_{n+3} = L_{n+1} + L_{n+2}` lets `omega` combine the new term with the inductive
hypothesis. -/
theorem lucas_sum_add_three (n : ℕ) :
    (∑ k ∈ Finset.range n, lucas (k + 1)) + 3 = lucas (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    -- The goal's RHS is `lucas (n + 1 + 2)`; state the recurrence in that exact index
    -- form so `omega` shares the `lucas (·)` atoms (it will not rewrite `n+1+2 ↦ n+3`).
    have hrec : lucas (n + 1 + 2) = lucas (n + 1) + lucas (n + 2) := lucas_add_two (n + 1)
    omega

/-- **Lucas partial-sum identity** `∑_{k=1}^{n} L_k = L_{n+2} − 3`.
Obtained from `lucas_sum_add_three` by transposing the `+ 3`; the `ℕ`-subtraction is
exact because `L_{n+2} ≥ 3`. -/
theorem lucas_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, lucas (k + 1)) = lucas (n + 2) - 3 := by
  have h := lucas_sum_add_three n
  omega

/-- **Lucas via Fibonacci.** `L_{n+1} = F_n + F_{n+2}`, equivalently `L_m = F_{m−1} + F_{m+1}`.
Two-step induction: both sides obey `x_{n+2} = x_n + x_{n+1}` and agree at the two base
indices, so the closed Fibonacci combination satisfies the Lucas recurrence.  This pins the
self-contained `lucas` above to Mathlib's standard `Nat.fib`. -/
theorem lucas_succ_eq_fib_add_fib (n : ℕ) :
    lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    -- IHs at `n` and `n+1`, restated in canonical index form.
    have h0' : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := h0
    have h1' : lucas (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := h1
    show lucas (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    -- Lucas recurrence, then eliminate every `lucas` so only aligned `fib` atoms remain
    -- (`omega` does not normalise `n+1+2` vs `n+3` inside an opaque `lucas (·)`).
    have el : lucas (n + 3) = lucas (n + 1) + lucas (n + 2) := lucas_add_two (n + 1)
    have f1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have f2 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    rw [el, h0', h1']
    omega

/-- Sanity check: `L_1 + L_2 + L_3 = 1 + 3 + 4 = 8 = L_5 − 3 = 11 − 3`. -/
example : (∑ k ∈ Finset.range 3, lucas (k + 1)) = 8 := by decide

/-- Sanity check of the headline identity at `n = 4`:
`1 + 3 + 4 + 7 = 15 = L_6 − 3 = 18 − 3`. -/
example : (∑ k ∈ Finset.range 4, lucas (k + 1)) = lucas 6 - 3 := by decide

end LucasSumOQ01
