/-
The Fibonacci shallow-diagonal sum of Pascal's triangle (OQ-01-OQ-01)

Parent entry `combinations-formula-oq-01` ("Extended Binomial Coefficient Identities")
records the shallow-diagonal Fibonacci connection only through worked `native_decide`
examples, leaving the general identity as its first open question:

  *Formal proof of the Fibonacci diagonal sum `Σ_j C(n−j, j) = F(n+1)`.*

This file proves it in general, axiom-free.  Summing along a shallow diagonal of
Pascal's triangle yields the Fibonacci numbers:

  `∑_{j=0}^{n} C(n−j, j) = F(n+1)`.

The proof reduces the identity to Mathlib's antidiagonal form
`Nat.fib_succ_eq_sum_choose` (`F(n+1) = ∑_{p ∈ antidiagonal n} C(p.1, p.2)`) by
rewriting the antidiagonal as a range sum and reflecting the index `j ↦ n − j`.

Main results:
* `fib_shallow_diagonal_alt` — the mirror form `∑_{k ∈ range (n+1)} C(k, n−k) = F(n+1)`.
* `fib_shallow_diagonal`     — `∑_{j ∈ range (n+1)} C(n−j, j) = F(n+1)`.
-/

import Mathlib

namespace CombinationsFormulaOQ01OQ01

open Finset

/-- **Fibonacci shallow-diagonal sum (mirror form).** `∑_{k} C(k, n−k) = F(n+1)`.
This is Mathlib's antidiagonal form `Nat.fib_succ_eq_sum_choose` rewritten as a range
sum. -/
theorem fib_shallow_diagonal_alt (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose k (n - k) = Nat.fib (n + 1) := by
  rw [Nat.fib_succ_eq_sum_choose, Finset.Nat.sum_antidiagonal_eq_sum_range_succ Nat.choose]

/-- **Fibonacci shallow-diagonal sum.** Summing `C(n−j, j)` over `j` recovers `F(n+1)`:
the shallow diagonals of Pascal's triangle are the Fibonacci numbers.  Obtained from the
mirror form by reflecting the summation index `j ↦ n − j`. -/
theorem fib_shallow_diagonal (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Nat.choose (n - j) j = Nat.fib (n + 1) := by
  rw [← fib_shallow_diagonal_alt,
      ← Finset.sum_range_reflect (fun k => Nat.choose k (n - k)) (n + 1)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e2 : n - (n - j) = j := by omega
  simp only [e1, e2]

end CombinationsFormulaOQ01OQ01
