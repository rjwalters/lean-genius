import Mathlib

/-
# Parity-indexed partial sums of Fibonacci numbers

The parent entry `FibonacciIdentitiesOQ03OQ02` proves the classical square-sum
identity `∑ Fᵢ² = Fₙ·Fₙ₊₁`, and its sibling `…OQ03OQ02OQ02` the Lucas analogue
`∑ Lᵢ² = Lₙ·Lₙ₊₁ − 2`. Both are *closed forms for a Fibonacci partial sum*.

Mathlib records only the **total** partial sum, `Nat.fib_succ_eq_succ_sum`:

  `fib (n+1) = (∑ k ∈ range n, fib k) + 1`,   i.e.   `F₀ + F₁ + ⋯ + Fₙ₋₁ = Fₙ₊₁ − 1`.

This entry supplies the **parity refinement** of that total: the partial sum
split according to whether the summand's index is odd or even. In Mathlib's
0-indexed convention (`fib 0 = 0`, `fib 1 = fib 2 = 1`, `fib 3 = 2`, …):

* **Odd indices** telescope to a *single* even-index Fibonacci, with no `−1`:

    `F₁ + F₃ + F₅ + ⋯ + F₂ₙ₋₁ = F₂ₙ`      (`fib_odd_index_sum`)

* **Even indices** carry the `−1` correction, landing one short of an odd-index
  Fibonacci:

    `F₂ + F₄ + F₆ + ⋯ + F₂ₙ = F₂ₙ₊₁ − 1`   (`fib_even_index_sum`)

The two are genuine complements: they **partition** the full range sum
(`fib_range_parity_split`), and adding them recovers `F₂ₙ₊₂ − 1`
(`fib_index_parity_total`, `fib_total_range_sum`) — the `n ↦ 2n` instance of
Mathlib's total-sum lemma, now split by parity. The `−1` therefore lives
entirely in the even-index half; the odd-index half is exactly telescoping.

Each identity is the textbook one-line induction: `Finset.sum_range_succ` peels
the top term and the Fibonacci recurrence `fib (k+2) = fib k + fib (k+1)`
(`Nat.fib_add_two`) closes the step. Integer forms are given so the even-index
`−1` is an honest subtraction rather than truncated `ℕ` subtraction.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ03OQ02OQ01

open Finset

/-- **Odd-index Fibonacci partial sum.** Summing the Fibonacci numbers at the
odd indices `1, 3, 5, …, 2n−1` gives a single even-index Fibonacci `F₂ₙ`, with
no correction term:

  `F₁ + F₃ + ⋯ + F₂ₙ₋₁ = F₂ₙ`.

One-line induction: peel the top summand `F₂ₙ₋₁`, apply the induction
hypothesis `⋯ = F₂ₙ₋₂`, and close with `F₂ₙ₋₂ + F₂ₙ₋₁ = F₂ₙ`. -/
theorem fib_odd_index_sum (n : ℕ) :
    ∑ i ∈ range n, Nat.fib (2 * i + 1) = Nat.fib (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [e, Nat.fib_add_two]

/-- **Even-index Fibonacci partial sum (additive form).** Summing the Fibonacci
numbers at the even indices `2, 4, 6, …, 2n` lands one short of an odd-index
Fibonacci:

  `(F₂ + F₄ + ⋯ + F₂ₙ) + 1 = F₂ₙ₊₁`.

The additive statement sidesteps truncated `ℕ` subtraction; see
`fib_even_index_sum_sub` for the `F₂ₙ₊₁ − 1` phrasing. -/
theorem fib_even_index_sum (n : ℕ) :
    (∑ i ∈ range n, Nat.fib (2 * i + 2)) + 1 = Nat.fib (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hrec : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
      have h : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by ring
      rw [h, Nat.fib_add_two]
    rw [hrec, ← ih]
    ring

/-- **Even-index partial sum, subtraction form.** `F₂ + F₄ + ⋯ + F₂ₙ = F₂ₙ₊₁ − 1`
in `ℕ` (honest, since `F₂ₙ₊₁ ≥ 1` for `n ≥ 0`). -/
theorem fib_even_index_sum_sub (n : ℕ) :
    ∑ i ∈ range n, Nat.fib (2 * i + 2) = Nat.fib (2 * n + 1) - 1 := by
  have h := fib_even_index_sum n
  omega

/-- **Parity partition of the range sum.** The first `2n` Fibonacci numbers
`F₁, …, F₂ₙ` split exactly into their odd-index and even-index parts — the two
partial sums above are complementary, covering the full range with no overlap. -/
theorem fib_range_parity_split (n : ℕ) :
    ∑ i ∈ range (2 * n), Nat.fib (i + 1)
      = (∑ i ∈ range n, Nat.fib (2 * i + 1)) + ∑ i ∈ range n, Nat.fib (2 * i + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
    -- indices `2*n+1+1` and `2*n+2` are defeq; normalise then close by `ring`
    have i1 : 2 * n + 1 + 1 = 2 * n + 2 := by ring
    rw [i1]
    ring

/-- **Consistency: odd + even parts recover `F₂ₙ₊₂`.** Adding the odd-index sum
(`= F₂ₙ`) and the even-index sum (`+1 = F₂ₙ₊₁`) gives `F₂ₙ + F₂ₙ₊₁ = F₂ₙ₊₂`, so
the single `−1` correction sits entirely in the even-index half. -/
theorem fib_index_parity_total (n : ℕ) :
    (∑ i ∈ range n, Nat.fib (2 * i + 1))
      + ((∑ i ∈ range n, Nat.fib (2 * i + 2)) + 1) = Nat.fib (2 * n + 2) := by
  rw [fib_odd_index_sum, fib_even_index_sum, Nat.fib_add_two]

/-- **Total range sum at an even bound.** The parity split, combined with the
consistency identity, recovers Mathlib's total-sum lemma specialised to `2n`:

  `(F₁ + F₂ + ⋯ + F₂ₙ) + 1 = F₂ₙ₊₂`. -/
theorem fib_total_range_sum (n : ℕ) :
    (∑ i ∈ range (2 * n), Nat.fib (i + 1)) + 1 = Nat.fib (2 * n + 2) := by
  rw [fib_range_parity_split]
  have := fib_index_parity_total n
  omega

/-- Integer form of the odd-index sum: `∑ F₂ᵢ₊₁ = F₂ₙ` over `ℤ`. -/
theorem fib_odd_index_sum_int (n : ℕ) :
    ∑ i ∈ range n, (Nat.fib (2 * i + 1) : ℤ) = (Nat.fib (2 * n) : ℤ) := by
  exact_mod_cast fib_odd_index_sum n

/-- Integer form of the even-index sum, with the `−1` as an honest subtraction:
`∑ F₂ᵢ₊₂ = F₂ₙ₊₁ − 1` over `ℤ`. -/
theorem fib_even_index_sum_int (n : ℕ) :
    ∑ i ∈ range n, (Nat.fib (2 * i + 2) : ℤ) = (Nat.fib (2 * n + 1) : ℤ) - 1 := by
  have h := fib_even_index_sum n
  have h2 : ((∑ i ∈ range n, Nat.fib (2 * i + 2) : ℕ) : ℤ) + 1
      = (Nat.fib (2 * n + 1) : ℤ) := by exact_mod_cast h
  push_cast at h2
  linarith

end FibonacciIdentitiesOQ03OQ02OQ01
