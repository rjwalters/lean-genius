import Mathlib

/-
# Even/Odd-Indexed and Alternating Lucas Partial Sums

## Open Question OQ-01-OQ-01 (extension of `lucas-sum-oq-01`)

The parent entry `lucas-sum-oq-01` proves the full telescoping partial sum
`∑_{k=1}^{n} L_k = L_{n+2} − 3` for the Lucas numbers `2, 1, 3, 4, 7, 11, 18, …`
(the Fibonacci recurrence `L_{k+2} = L_k + L_{k+1}` with `L_0 = 2`, `L_1 = 1`).

Splitting the sum by parity of the index gives two further telescoping identities, and
alternating the signs gives a third.  All three are subtraction-free at heart:

1. **Even-indexed.**  `∑_{k=1}^{n} L_{2k} = L_{2n+1} − 1`.
   e.g. `L_2 + L_4 = 3 + 7 = 10 = L_5 − 1 = 11 − 1`.

2. **Odd-indexed.**   `∑_{k=1}^{n} L_{2k−1} = L_{2n} − 2`.
   e.g. `L_1 + L_3 = 1 + 4 = 5 = L_4 − 2 = 7 − 2`.

3. **Alternating.**   `∑_{k=0}^{m} (−1)^k L_k = (−1)^m L_{m−1} + 3` (for `m ≥ 1`).
   The closed form is again *Lucas-only* — no Fibonacci term is needed — because
   `L_{m+1} − L_{m−1} = L_m` collapses the telescoping remainder.
   e.g. `L_0 − L_1 + L_2 − L_3 + L_4 = 2 − 1 + 3 − 4 + 7 = 7 = L_3 + 3 = 4 + 3`.

## What is proved here

Each identity is proved in a subtraction-free "`+ c = L_j`" form by induction directly
from the recurrence (the exact statement the telescoping argument produces, avoiding all
`ℕ`-subtraction edge cases), then the headline subtracted form is read off.

* `lucas_even_sum_add_one` / `lucas_even_sum` — even-indexed.
* `lucas_odd_sum_add_two`  / `lucas_odd_sum`  — odd-indexed.
* `lucas_alt_sum` — the alternating sum, stated over `ℤ` (signs force the integer setting),
  in the subtraction-free shifted form `∑_{k<n+2} (−1)^k L_k = (−1)^{n+1} L_n + 3`.

The 1-indexed sums `∑_{k=1}^{n} L_{2k}` and `∑_{k=1}^{n} L_{2k−1}` are encoded as
`∑ k ∈ Finset.range n, lucas (2*k+2)` and `∑ k ∈ Finset.range n, lucas (2*k+1)`.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSumOQ01OQ01

open Finset

/-- The Lucas numbers `2, 1, 3, 4, 7, 11, …` — the Fibonacci recurrence with the
alternative initial data `L_0 = 2`, `L_1 = 1`.  (Self-contained copy of the definition
from the parent entry `lucas-sum-oq-01`.) -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining Lucas recurrence `L_{n+2} = L_n + L_{n+1}`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-! ### Even-indexed partial sum -/

/-- **Even-indexed telescoping sum (subtraction-free).**
`(∑_{k=1}^{n} L_{2k}) + 1 = L_{2n+1}`.

Induction on `n`.  Base: `0 + 1 = L_1 = 1`.  Step: `Finset.sum_range_succ` peels off the
new term `L_{2n+2}`; the Lucas recurrence `L_{2n+3} = L_{2n+1} + L_{2n+2}` lets `omega`
combine it with the inductive hypothesis. -/
theorem lucas_even_sum_add_one (n : ℕ) :
    (∑ k ∈ Finset.range n, lucas (2 * k + 2)) + 1 = lucas (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hidx : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
    have hrec : lucas (2 * n + 3) = lucas (2 * n + 1) + lucas (2 * n + 2) :=
      lucas_add_two (2 * n + 1)
    rw [hidx]
    omega

/-- **Even-indexed Lucas partial sum** `∑_{k=1}^{n} L_{2k} = L_{2n+1} − 1`.
Read off from `lucas_even_sum_add_one`; the `ℕ`-subtraction is exact since `L_{2n+1} ≥ 1`. -/
theorem lucas_even_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, lucas (2 * k + 2)) = lucas (2 * n + 1) - 1 := by
  have h := lucas_even_sum_add_one n
  omega

/-! ### Odd-indexed partial sum -/

/-- **Odd-indexed telescoping sum (subtraction-free).**
`(∑_{k=1}^{n} L_{2k−1}) + 2 = L_{2n}`.

Induction on `n`.  Base: `0 + 2 = L_0 = 2`.  Step: the new term `L_{2n+1}` combines with
the inductive hypothesis via `L_{2n+2} = L_{2n} + L_{2n+1}`. -/
theorem lucas_odd_sum_add_two (n : ℕ) :
    (∑ k ∈ Finset.range n, lucas (2 * k + 1)) + 2 = lucas (2 * n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hidx : 2 * (n + 1) = 2 * n + 2 := by ring
    have hrec : lucas (2 * n + 2) = lucas (2 * n) + lucas (2 * n + 1) :=
      lucas_add_two (2 * n)
    rw [hidx]
    omega

/-- **Odd-indexed Lucas partial sum** `∑_{k=1}^{n} L_{2k−1} = L_{2n} − 2`.
Read off from `lucas_odd_sum_add_two`; the `ℕ`-subtraction is exact since `L_{2n} ≥ 2`. -/
theorem lucas_odd_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, lucas (2 * k + 1)) = lucas (2 * n) - 2 := by
  have h := lucas_odd_sum_add_two n
  omega

/-! ### Alternating partial sum -/

/-- **Alternating Lucas partial sum** (over `ℤ`, since the signs force the integer setting).
In subtraction-free shifted form:
`∑_{k=0}^{n+1} (−1)^k L_k = (−1)^{n+1} L_n + 3`.

Equivalently `∑_{k=0}^{m} (−1)^k L_k = (−1)^m L_{m−1} + 3` for `m = n + 1 ≥ 1`.  The closed
form is Lucas-only: in the induction step the two new sign-weighted terms collapse via the
recurrence `L_{n+2} − L_n = L_{n+1}`, leaving no Fibonacci remainder. -/
theorem lucas_alt_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), (-1 : ℤ) ^ k * (lucas k : ℤ))
      = (-1 : ℤ) ^ (n + 1) * (lucas n : ℤ) + 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    -- The two new sign-weighted terms collapse via the Lucas recurrence.
    have hrec : ((lucas (n + 2) : ℤ)) = (lucas n : ℤ) + (lucas (n + 1) : ℤ) := by
      have := lucas_add_two n
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) this
    have hpow : (-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ n := by
      rw [pow_add]; ring
    have hpow1 : (-1 : ℤ) ^ (n + 1) = -(-1 : ℤ) ^ n := by
      rw [pow_succ]; ring
    rw [hrec, hpow, hpow1]
    ring

/-! ### Sanity checks -/

/-- `L_2 + L_4 = 3 + 7 = 10 = L_5 − 1`. -/
example : (∑ k ∈ Finset.range 2, lucas (2 * k + 2)) = lucas 5 - 1 := by decide

/-- `L_1 + L_3 = 1 + 4 = 5 = L_4 − 2`. -/
example : (∑ k ∈ Finset.range 2, lucas (2 * k + 1)) = lucas 4 - 2 := by decide

/-- `L_0 − L_1 + L_2 − L_3 + L_4 = 2 − 1 + 3 − 4 + 7 = 7 = L_3 + 3`. -/
example :
    (∑ k ∈ Finset.range 5, (-1 : ℤ) ^ k * (lucas k : ℤ)) = (lucas 3 : ℤ) + 3 := by
  decide

end LucasSumOQ01OQ01
