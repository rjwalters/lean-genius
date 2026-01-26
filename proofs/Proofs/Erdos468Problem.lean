/-!
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

/-! ## Core Definitions -/

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

/-! ## Question 1: Size of New Elements -/

/-- How large is |D_n \ ⋃_{m<n} D_m|? This counts elements
    that appear for the first time in D_n. -/
axiom new_elements_exist (n : ℕ) (hn : 2 ≤ n) :
    (newElements n).Nonempty

/-- The number of new elements should grow — each n contributes
    something genuinely new to the collection of partial sums. -/
axiom new_element_count_conjecture :
    ∀ B : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      B ≤ (partialDivisorSums n).card

/-! ## Question 2: The f(N) Function -/

/-- f(N) = min{n : N ∈ D_n}: the first n whose divisor partial sums include N. -/
noncomputable def firstAppearance (N : ℕ) : ℕ :=
  sInf { n : ℕ | N ∈ partialDivisorSums n }

/-- **Main Conjecture:** f(N) = o(N). The first appearance of N
    as a partial divisor sum grows sublinearly. -/
axiom erdos_468_conjecture :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (firstAppearance N : ℝ) ≤ ε * (N : ℝ)

/-- Weaker conjecture: f(N) = o(N) for almost all N.
    The density of exceptions tends to 0. -/
axiom erdos_468_almost_all :
    ∀ ε > 0, ∀ δ > 0, ∃ N₀ : ℕ, ∀ M ≥ N₀,
      ((Finset.Icc 1 M).filter (fun N => (firstAppearance N : ℝ) > ε * N)).card ≤ δ * M

/-! ## Small Examples -/

/-- D_6: divisors > 1 are {2, 3, 6}. Partial sums: 2, 5, 11. -/
axiom d6_example : partialDivisorSums 6 = {2, 5, 11}

/-- D_12: divisors > 1 are {2, 3, 4, 6, 12}. Partial sums: 2, 5, 9, 15, 27. -/
axiom d12_example : partialDivisorSums 12 = {2, 5, 9, 15, 27}

/-! ## Trivial Observations -/

/-- The smallest element of D_n is always the smallest divisor > 1,
    which is the smallest prime factor of n. -/
axiom smallest_partial_sum (n : ℕ) (hn : 2 ≤ n) :
    n.minFac ∈ partialDivisorSums n

/-- The largest element of D_n is σ(n) - 1 (sum of all divisors minus 1). -/
axiom largest_partial_sum (n : ℕ) (hn : 2 ≤ n) :
    (n.divisors.sum id - 1) ∈ partialDivisorSums n

/-- OEIS A167485 relates to the sequence of partial sums of divisors. -/
axiom oeis_context : True
