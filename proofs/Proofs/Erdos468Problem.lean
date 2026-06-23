/-
# Erdős Problem #468 — Partial Sums of Divisors

For a positive integer n, let D_n be the set of partial sums
d₁, d₁+d₂, d₁+d₂+d₃, ... where 1 < d₁ < d₂ < ⋯ are the
divisors of n (excluding 1) in increasing order.

**Questions:**
1. How large is D_n \ ⋃_{m<n} D_m? (New elements in D_n.)
2. If f(N) = min{n : N ∈ D_n}, is f(N) = o(N)? At least for almost all N?

**Status: OPEN.**

Reference: https://erdosproblems.com/468
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The divisors of n greater than 1, sorted in increasing order. -/
noncomputable def properDivisorsSorted (n : ℕ) : List ℕ :=
  ((n.divisors.filter (· > 1)).sort (· ≤ ·))

/-- The set of partial sums of the proper divisors of n.
    D_n = {d₁, d₁+d₂, d₁+d₂+d₃, ...} where d₁ < d₂ < ⋯
    are divisors of n greater than 1. -/
noncomputable def partialDivisorSums (n : ℕ) : Finset ℕ :=
  let divs := properDivisorsSorted n
  (List.range divs.length).map (fun k => (divs.take (k + 1)).sum) |>.toFinset

/-- The union of all D_m for m < n. -/
noncomputable def previousPartialSums (n : ℕ) : Set ℕ :=
  ⋃ m ∈ Finset.range n, ↑(partialDivisorSums m)

/-- The new elements in D_n: those not appearing in any earlier D_m. -/
noncomputable def newElements (n : ℕ) : Set ℕ :=
  ↑(partialDivisorSums n) \ previousPartialSums n

/- ## Question 1: Size of New Elements -/

/- ## Question 2: The f(N) Function -/

/-- f(N) = min{n : N ∈ D_n}: the first n whose divisor partial sums include N. -/
noncomputable def firstAppearance (N : ℕ) : ℕ :=
  sInf { n : ℕ | N ∈ partialDivisorSums n }

/- ## Small Examples -/

/- ## Trivial Observations -/

/- OEIS A167485 relates to the sequence of partial sums of divisors. -/
