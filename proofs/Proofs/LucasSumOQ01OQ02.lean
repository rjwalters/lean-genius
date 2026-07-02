import Mathlib

/-
# Weighted and Squared Lucas Partial Sums: `∑ k·L_k` and `∑ L_k²`

## Open Question OQ-01-OQ-02 (from `lucas-sum-oq-01`)

The parent entry `lucas-sum-oq-01` proves the linear Lucas telescoping sum
`∑_{k=1}^{n} L_k = L_{n+2} − 3` and records the Fibonacci bridge
`L_{n+1} = F_n + F_{n+2}`.  Its second open question asks:

> Derive a Lucas analogue of `∑ k·F_k` or `∑ F_k²` and relate it to the Fibonacci
> versions through the bridge `L_{n+1} = F_n + F_{n+2}`.

This entry answers it for **both** weighted and squared sums, over the companion
sequence `L_0 = 2, L_1 = 1, L_{n+2} = L_n + L_{n+1}`:

* `lucas_sq_sum`      —  `∑_{k=0}^{n} L_k² = L_n · L_{n+1} + 2`.
* `weighted_lucas_sum` —  `∑_{k=0}^{n} k·L_k = n·L_{n+2} − L_{n+3} + 4`.

Both close under a **one-step induction** driven purely by the Lucas recurrence,
stated in subtraction-free `(∑ …) + c = …` form so `omega`/`ring` finish each step.

## The Fibonacci comparison and bridge

For contrast we prove the classical Fibonacci square-sum

* `fib_sq_sum`  —  `∑_{k=0}^{n} F_k² = F_n · F_{n+1}`

by the same one-step telescoping, and then **relate the two** through the parent's
bridge `L_{n+1} = F_n + F_{n+2}`:

* `lucas_sq_sum_fib`  —  `∑_{k=0}^{n+1} L_k² = (F_n+F_{n+2})·(F_{n+1}+F_{n+3}) + 2`.

The Lucas square-sum thus factors, via the bridge, into a product of *sums of two
Fibonacci numbers* — the exact way the two sequences are tied together.

## The telescoped constants

The squared sum telescopes as `L_k² = L_k·L_{k+1} − L_{k−1}·L_k`, giving the
closed constant `+2 = −L_{−1}·L_0 = −(−1)·2`.  The weighted sum uses the
Abel-summation shape `k·L_k = k·(L_{k+2} − L_{k+1})`, producing the `n·L_{n+2}`
head term and the `−L_{n+3} + 4` correction.  Both correction constants are
recorded first in subtraction-free form so `ℕ`-subtraction never appears mid-proof.

## References

- The linear Lucas sum `∑ L_k = L_{n+2} − 3` and the bridge `L_{n+1} = F_n + F_{n+2}`
  (parent family `lucas-sum-oq-01`).
- `∑ F_k² = F_n·F_{n+1}` and `L_k² − 5F_k² = 4(−1)^k` (Vajda, *Fibonacci & Lucas
  Numbers*, identities (11), (28)).

## Axioms: 0 | Sorries: 0
-/

namespace LucasSumOQ01OQ02

open Finset

/-- The Lucas numbers `2, 1, 3, 4, 7, 11, …` — the Fibonacci recurrence with the
alternative initial data `L_0 = 2`, `L_1 = 1`.  Same self-contained definition as
the parent `lucas-sum-oq-01`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining Lucas recurrence `L_{n+2} = L_n + L_{n+1}`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-! ## Squared Lucas partial sum `∑_{k=0}^{n} L_k² = L_n · L_{n+1} + 2` -/

/-- **Squared Lucas partial sum.** `∑_{k=0}^{n} L_k² = L_n · L_{n+1} + 2`.

One-step induction.  Peeling `L_{n+1}²` and substituting the recurrence
`L_{n+2} = L_n + L_{n+1}` reduces the step to
`L_n·L_{n+1} + L_{n+1}² = L_{n+1}·(L_n + L_{n+1})`, closed by `ring`. -/
theorem lucas_sq_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), lucas k ^ 2) = lucas n * lucas (n + 1) + 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : lucas (n + 1 + 1) = lucas n + lucas (n + 1) := lucas_add_two n
    rw [hrec]; ring

/-! ## Weighted Lucas partial sum `∑_{k=0}^{n} k·L_k = n·L_{n+2} − L_{n+3} + 4` -/

/-- **Weighted Lucas partial sum (subtraction-free).**
`(∑_{k=0}^{n} k·L_k) + L_{n+3} = n·L_{n+2} + 4`.

One-step induction: peeling the new term `(n+1)·L_{n+1}` and expanding the two
recurrences `L_{n+4} = L_{n+2}+L_{n+3}`, `L_{n+3} = L_{n+1}+L_{n+2}` lets `omega`
combine everything with the inductive hypothesis. -/
theorem weighted_lucas_sum_add (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k * lucas k) + lucas (n + 3) = n * lucas (n + 2) + 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    -- recurrences at the two indices the step needs, in canonical form
    have h4 : lucas (n + 1 + 3) = lucas (n + 2) + lucas (n + 3) := lucas_add_two (n + 2)
    have e2 : lucas (n + 1 + 2) = lucas (n + 3) := rfl
    -- distribute `(n+1)` across the recurrence `L_{n+3} = L_{n+1} + L_{n+2}` so `omega`
    -- can treat each `(n+1)·L`, `n·L` product as a consistent atom
    have key : (n + 1) * lucas (n + 3)
        = (n + 1) * lucas (n + 1) + (n + 1) * lucas (n + 2) := by
      have h2 : lucas (n + 3) = lucas (n + 1) + lucas (n + 2) := lucas_add_two (n + 1)
      rw [h2]; ring
    have hd : (n + 1) * lucas (n + 2) = n * lucas (n + 2) + lucas (n + 2) := by ring
    rw [Finset.sum_range_succ, h4, e2]
    omega

/-- **Weighted Lucas partial sum** `∑_{k=0}^{n} k·L_k = n·L_{n+2} − L_{n+3} + 4`
(truncated subtraction over `ℕ`; well-defined since `n·L_{n+2} + 4 ≥ L_{n+3}`). -/
theorem weighted_lucas_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k * lucas k) = n * lucas (n + 2) + 4 - lucas (n + 3) := by
  have h := weighted_lucas_sum_add n
  omega

/-! ## The Fibonacci square-sum and the bridge -/

/-- **Fibonacci square-sum.** `∑_{k=0}^{n} F_k² = F_n · F_{n+1}`, by the same
one-step telescoping `F_n·F_{n+1} + F_{n+1}² = F_{n+1}·F_{n+2}`. -/
theorem fib_sq_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Nat.fib k ^ 2) = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rw [hrec]; ring

/-- **Lucas via Fibonacci.** `L_{n+1} = F_n + F_{n+2}` (parent's bridge, re-proved
here so the file is self-contained).  Two-step induction on the shared recurrence. -/
theorem lucas_succ_eq_fib_add_fib (n : ℕ) :
    lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    have h0' : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := h0
    have h1' : lucas (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := h1
    show lucas (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    have el : lucas (n + 3) = lucas (n + 1) + lucas (n + 2) := lucas_add_two (n + 1)
    have f1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have f2 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    rw [el, h0', h1']
    omega

/-- **The bridge corollary.** The squared Lucas partial sum factors, via
`L_{m+1} = F_m + F_{m+2}`, into a product of sums of two Fibonacci numbers:
`∑_{k=0}^{n+1} L_k² = (F_n+F_{n+2})·(F_{n+1}+F_{n+3}) + 2`. -/
theorem lucas_sq_sum_fib (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), lucas k ^ 2)
      = (Nat.fib n + Nat.fib (n + 2)) * (Nat.fib (n + 1) + Nat.fib (n + 3)) + 2 := by
  rw [lucas_sq_sum (n + 1), lucas_succ_eq_fib_add_fib n,
      show lucas (n + 1 + 1) = Nat.fib (n + 1) + Nat.fib (n + 3) from
        lucas_succ_eq_fib_add_fib (n + 1)]

/-! ## Numerical sanity checks -/

/-- `L₀² + L₁² + L₂² + L₃² = 4 + 1 + 9 + 16 = 30 = L₃·L₄ + 2 = 4·7 + 2`. -/
theorem lucas_sq_sum_example : (∑ k ∈ Finset.range 4, lucas k ^ 2) = 30 := by decide

/-- `0·L₀ + 1·L₁ + 2·L₂ + 3·L₃ = 0 + 1 + 6 + 12 = 19 = 3·L₅ − L₆ + 4 = 33 − 18 + 4`. -/
theorem weighted_lucas_sum_example :
    (∑ k ∈ Finset.range 4, k * lucas k) = 19 := by decide

/-- `F₀² + … + F₄² = 0 + 1 + 1 + 4 + 9 = 15 = F₄·F₅ = 3·5`. -/
theorem fib_sq_sum_example : (∑ k ∈ Finset.range 5, Nat.fib k ^ 2) = 15 := by decide

end LucasSumOQ01OQ02
