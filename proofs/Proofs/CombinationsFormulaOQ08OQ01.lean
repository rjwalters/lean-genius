import Mathlib

/-
# The Fibonacci Recurrence as a Shadow of Pascal's Rule (OQ-08-OQ-01)

Parent entry `combinations-formula-oq-08` proves that the Fibonacci numbers are the
sums along the shallow diagonals of Pascal's triangle:

  `fib (n + 1) = ∑ k ∈ range (n + 1), C(n - k, k)`        (`fib_eq_sum_range_choose`).

That identity is established by *reindexing* Mathlib's antidiagonal form.  This
follow-up takes the next, genuinely combinatorial step: it derives the Fibonacci
recurrence `F_{n+2} = F_{n+1} + F_n` **directly from the shallow-diagonal sums**, by
applying Pascal's rule `C(a+1, b+1) = C(a, b) + C(a, b+1)` to each diagonal term — no
appeal to `Nat.fib_add_two`, no generating functions, no matrix powers.

Write `D n := ∑ k ∈ range (n + 1), C(n - k, k)` for the `n`-th shallow-diagonal total.
The centerpiece is

  `D_recurrence : D (n + 2) = D (n + 1) + D n`,

proved purely by term-by-term Pascal expansion and reindexing of finite sums.  Combined
with the parent identity `D n = fib (n + 1)`, this *reproves* the Fibonacci recurrence
combinatorially (`fib_recurrence_via_pascal`), exhibiting it as a shadow of Pascal's
rule.

The second half links the diagonals to the **Lucas partial-sum identity**

  `∑ i ∈ range n, fib i = fib (n + 1) - 1`                 (`fib_partial_sum_sub`),

and re-expresses it as a statement about the shallow-diagonal totals:

  `∑ i ∈ range n, D i = fib (n + 2) - 1`                   (`shallow_diag_partial_sum`).

## Proof of the recurrence (sketch)

Peeling the `k = 0` term of `D (n + 2)` with `Finset.sum_range_succ'` and discarding the
vanishing top term `C(0, n + 2) = 0` with `Finset.sum_range_succ` gives

  `D (n + 2) = (∑ k ∈ range (n + 1), C(n + 1 - k, k + 1)) + 1`.

Peeling the `k = 0` term of `D (n + 1)` likewise gives

  `D (n + 1) = (∑ k ∈ range (n + 1), C(n - k, k + 1)) + 1`,

while `D n = ∑ k ∈ range (n + 1), C(n - k, k)`.  For `k ≤ n` we have
`n + 1 - k = (n - k) + 1`, so Pascal's rule yields term-by-term

  `C(n + 1 - k, k + 1) = C(n - k, k) + C(n - k, k + 1)`,

and summing this identity over `range (n + 1)` matches the two sides.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ08OQ01

open Finset

/-- `D n` is the total of the `n`-th shallow diagonal of Pascal's triangle:
    `D n = C(n, 0) + C(n - 1, 1) + C(n - 2, 2) + ⋯`. -/
def D (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k

/-- **Parent identity (`combinations-formula-oq-08`, `fib_eq_sum_range_choose`).**
    The shallow-diagonal formula `fib (n + 1) = ∑ k ∈ range (n+1), C(n - k, k)`, reproved
    inline here so this file stands alone.  It reindexes Mathlib's antidiagonal form
    `Nat.fib_succ_eq_sum_choose` via `sum_antidiagonal_eq_sum_range_succ` and the index
    reflection `k ↦ n - k`. -/
theorem fib_eq_sum_range_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k := by
  rw [Nat.fib_succ_eq_sum_choose,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose i j) n,
      ← Finset.sum_range_reflect (fun k => Nat.choose (n - k) k) (n + 1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk]

/-- The shallow-diagonal total equals a Fibonacci number, recorded in terms of `D`. -/
theorem D_eq_fib (n : ℕ) : D n = Nat.fib (n + 1) :=
  (fib_eq_sum_range_choose n).symm

/-- **Pascal expansion of one diagonal term.**
    For `k ≤ n`, the entry on diagonal `n + 1` splits into the two entries directly
    below it on diagonal `n`, by Pascal's rule.  This is the single arithmetic fact that
    drives the whole recurrence. -/
theorem choose_shift_succ {n k : ℕ} (hk : k ≤ n) :
    Nat.choose (n + 1 - k) (k + 1) = Nat.choose (n - k) k + Nat.choose (n - k) (k + 1) := by
  have h : n + 1 - k = (n - k) + 1 := by omega
  rw [h, Nat.choose_succ_succ]

/-- After peeling the `k = 0` term and dropping the vanishing top term, the diagonal
    total `D (n + 2)` is a single sum over `range (n + 1)` plus the constant `1`. -/
theorem D_add_two_peel (n : ℕ) :
    D (n + 2) = (∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) (k + 1)) + 1 := by
  unfold D
  rw [Finset.sum_range_succ' (fun k => Nat.choose (n + 2 - k) k) (n + 2)]
  -- peel `k = 0`: the constant term is `C(n + 2, 0) = 1` (only the `_ 0` term is touched)
  simp only [Nat.choose_zero_right]
  -- split off the top term `k = n + 1` of the shifted sum
  rw [Finset.sum_range_succ]
  -- drop the vanishing top term `C(n + 2 - (n + 2), n + 2) = C(0, n + 2) = 0`
  rw [Nat.choose_eq_zero_of_lt (show n + 2 - (n + 1 + 1) < n + 1 + 1 by omega), add_zero]
  -- match the remaining sum term-by-term: `n + 2 - (k + 1) = n + 1 - k`
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

/-- After peeling its `k = 0` term, the diagonal total `D (n + 1)` is a single sum over
    `range (n + 1)` plus the constant `1`. -/
theorem D_add_one_peel (n : ℕ) :
    D (n + 1) = (∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) (k + 1)) + 1 := by
  unfold D
  rw [Finset.sum_range_succ' (fun k => Nat.choose (n + 1 - k) k) (n + 1)]
  -- peel `k = 0`: the constant term is `C(n + 1, 0) = 1` (only the `_ 0` term is touched)
  simp only [Nat.choose_zero_right]
  -- match the remaining sum term-by-term: `n + 1 - (k + 1) = n - k`
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

/-- **The shallow-diagonal recurrence — the combinatorial core.**
    The diagonal totals satisfy the Fibonacci recurrence, derived purely by applying
    Pascal's rule to each diagonal term.  No use of `Nat.fib_add_two`. -/
theorem D_recurrence (n : ℕ) : D (n + 2) = D (n + 1) + D n := by
  rw [D_add_two_peel, D_add_one_peel]
  unfold D
  -- LHS sum: expand each term by Pascal's rule (valid since `k ≤ n` on `range (n+1)`)
  have hL : (∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) (k + 1))
      = ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (n - k) k + Nat.choose (n - k) (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [choose_shift_succ hk]
  rw [hL, Finset.sum_add_distrib]
  ring

/-- **The Fibonacci recurrence, reproved as a shadow of Pascal's rule.**
    Combining the shallow-diagonal recurrence `D_recurrence` with the parent identity
    `D n = fib (n + 1)` recovers `fib (n + 2) = fib (n + 1) + fib n` — obtained here
    entirely from Pascal's rule on the diagonals, independently of `Nat.fib_add_two`. -/
theorem fib_recurrence_via_pascal (n : ℕ) :
    Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
  have h := D_recurrence n
  rw [D_eq_fib, D_eq_fib, D_eq_fib] at h
  exact h

/-! ### Link to the Lucas partial-sum identity -/

/-- **Lucas partial-sum identity (subtraction-free form).**
    `(∑ i ∈ range n, fib i) + 1 = fib (n + 1)`.  Proved by induction using
    `Nat.fib_add_two`; stated without truncated subtraction. -/
theorem fib_partial_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, Nat.fib i) + 1 = Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    -- `(∑_{i<m} fib i + fib m) + 1 = (∑_{i<m} fib i + 1) + fib m = fib (m+1) + fib m`
    have : (∑ i ∈ Finset.range m, Nat.fib i) + Nat.fib m + 1
        = ((∑ i ∈ Finset.range m, Nat.fib i) + 1) + Nat.fib m := by ring
    rw [this, ih, Nat.fib_add_two]
    ring

/-- **Lucas partial-sum identity (textbook form).**
    `∑ i ∈ range n, fib i = fib (n + 1) - 1`. -/
theorem fib_partial_sum_sub (n : ℕ) :
    (∑ i ∈ Finset.range n, Nat.fib i) = Nat.fib (n + 1) - 1 := by
  have h := fib_partial_sum n
  omega

/-- **Partial sums of the shallow-diagonal totals.**
    Summing the diagonal totals `D 0, D 1, …, D (n-1)` gives `fib (n + 2) - 1`, the
    Lucas partial-sum identity recast in terms of the shallow diagonals.  Each `D i`
    equals `fib (i + 1)`, so this is `fib 1 + fib 2 + ⋯ + fib n = fib (n + 2) - 1`. -/
theorem shallow_diag_partial_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, D i) = Nat.fib (n + 2) - 1 := by
  have hrw : (∑ i ∈ Finset.range n, D i)
      = ∑ i ∈ Finset.range n, Nat.fib (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    exact D_eq_fib i
  rw [hrw]
  -- `∑_{i<n} fib (i+1) = (∑_{i<n+1} fib i) - fib 0 = fib (n+2) - 1`
  have hshift : (∑ i ∈ Finset.range n, Nat.fib (i + 1))
      = (∑ i ∈ Finset.range (n + 1), Nat.fib i) - Nat.fib 0 := by
    rw [Finset.sum_range_succ' Nat.fib n]
    simp
  rw [hshift, fib_partial_sum_sub]
  simp

/-- Sanity check: `D 6 = fib 7 = 13`, from `C(6,0)+C(5,1)+C(4,2)+C(3,3) = 1+5+6+1 = 13`. -/
example : D 6 = 13 := by decide

/-- Sanity check on the recurrence: `D 6 = D 5 + D 4`, i.e. `13 = 8 + 5`. -/
example : D 6 = D 5 + D 4 := by decide

/-- Sanity check on the partial sum: `D 0 + D 1 + D 2 + D 3 = fib 6 - 1 = 7`,
    i.e. `1 + 1 + 2 + 3 = 7`. -/
example : (∑ i ∈ Finset.range 4, D i) = 7 := by decide

end CombinationsFormulaOQ08OQ01
