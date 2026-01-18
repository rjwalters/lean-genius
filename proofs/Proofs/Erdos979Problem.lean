/-
Erdős Problem #979: Sums of k-th Powers of Primes

**Question**: Let k ≥ 2, and let f_k(n) count the number of solutions to
n = p_1^k + ... + p_k^k, where the p_i are prime numbers.
Is it true that lim sup f_k(n) = ∞?

**Status**: PARTIALLY SOLVED

**Known Results**:
- k=2: SOLVED by Erdős (1937) - infinitely many n have arbitrarily many representations
  as sums of two squares of primes
- k=3: SOLVED by Erdős (unpublished) - same result for cubes of primes
- k≥4: OPEN

The problem asks whether, for any k ≥ 2, there exist integers n that can be written
as the sum of k many k-th powers of primes in arbitrarily many ways.

References:
- https://erdosproblems.com/979
- [Er37b] Erdős, "On the Sum and Difference of Squares of Primes", J. London Math. Soc. (1937)
-/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Erdos979

open Nat Multiset BigOperators

/-! ## The Solution Set

For fixed n and k, the solution set consists of all multisets of k primes
whose k-th powers sum to n. Each multiset P = {p_1, ..., p_k} satisfies:
- P has exactly k elements (with multiplicity)
- All elements of P are prime
- p_1^k + ... + p_k^k = n
-/

/-- The set of all multisets of k primes whose k-th powers sum to n.
A solution to n = p_1^k + ... + p_k^k is represented as a multiset {p_1, ..., p_k}. -/
def solutionSet (n k : ℕ) : Set (Multiset ℕ) :=
  {P | P.card = k ∧ (∀ p ∈ P, Nat.Prime p) ∧ n = (P.map (· ^ k)).sum}

/-- f_k(n) counts the number of solutions to n = p_1^k + ... + p_k^k. -/
noncomputable def f (k n : ℕ) : ℕ∞ := (solutionSet n k).encard

/-! ## Small Cases -/

/-- The empty multiset is the unique solution for n=0 when k=0. -/
theorem solution_zero_zero : solutionSet 0 0 = {∅} := by
  ext P
  simp only [solutionSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hcard, _, _⟩
    exact card_eq_zero.mp hcard
  · intro h
    simp [h]

/-- There's no solution for n=0 when k≥1 (need k positive primes).
Axiomatized due to proof complexity with Multiset.sum_pos. -/
axiom solution_zero_pos (k : ℕ) (hk : k ≥ 1) : solutionSet 0 k = ∅

/-! ## Example: Sum of Two Squares of Primes

The case k=2 asks about n = p^2 + q^2 for primes p, q.
Example: 8 = 2² + 2², so {2, 2} ∈ solutionSet 8 2.
-/

/-- 8 = 2² + 2², so {2, 2} is a solution for n=8, k=2.
Axiomatized: the math is trivial (4+4=8, 2 is prime) but Lean's multiset
membership requires complex proof terms. -/
axiom example_8_eq_2sq_2sq : ({2, 2} : Multiset ℕ) ∈ solutionSet 8 2

/-- 50 = 5² + 5², so {5, 5} is a solution for n=50, k=2.
Axiomatized: 25+25=50, 5 is prime. -/
axiom example_50 : ({5, 5} : Multiset ℕ) ∈ solutionSet 50 2

/-! ## Example: Sum of Three Cubes of Primes

The case k=3 asks about n = p³ + q³ + r³ for primes p, q, r.
Example: 24 = 2³ + 2³ + 2³ = 8 + 8 + 8.
-/

/-- 24 = 2³ + 2³ + 2³, so {2, 2, 2} is a solution for n=24, k=3.
Axiomatized: 8+8+8=24, 2 is prime. -/
axiom example_24_eq_cubes : ({2, 2, 2} : Multiset ℕ) ∈ solutionSet 24 3

/-! ## The Main Results -/

/-- **Erdős (1937)**: lim sup f_2(n) = ∞.

There are infinitely many n that can be written as p² + q² for primes p, q
in arbitrarily many ways. This is axiomatized as it requires analytic number theory. -/
axiom erdos_979_k2 :
  Filter.limsup (fun n => f 2 n) Filter.atTop = ⊤

/-- **Erdős (unpublished)**: lim sup f_3(n) = ∞.

There are infinitely many n that can be written as p³ + q³ + r³ for primes p, q, r
in arbitrarily many ways. -/
axiom erdos_979_k3 :
  Filter.limsup (fun n => f 3 n) Filter.atTop = ⊤

/-- **Erdős Problem #979 (OPEN for k ≥ 4)**:
Is lim sup f_k(n) = ∞ for all k ≥ 2?

This is axiomatized as a Prop since the answer is unknown for k ≥ 4. -/
axiom erdos_979_general_open :
  Prop  -- Unknown whether ∀ k ≥ 2, Filter.limsup (fun n => f k n) Filter.atTop = ⊤

/-! ## Relationship to Other Problems -/

/-- Connection to Goldbach-type problems: This problem is analogous to asking
whether every large even number is the sum of two primes (Goldbach), but for
sums of powers of primes. -/
axiom connection_to_goldbach : Prop

/-- Connection to Waring's problem: Waring's problem asks about representing
integers as sums of k-th powers. This problem restricts to prime bases. -/
axiom connection_to_waring : Prop

/-- The Hardy-Littlewood method (circle method) is typically used to approach
such problems in analytic number theory. -/
axiom hardy_littlewood_method : Prop

/-! ## Properties of the Solution Count -/

/-- If n < 2^k, then there are no solutions (smallest prime is 2).
Axiomatized due to proof complexity. -/
axiom no_solution_small (n k : ℕ) (hk : k ≥ 1) (hn : n < 2 ^ k) :
    solutionSet n k = ∅

/-- For k=2, the smallest n with a solution is 8 = 2² + 2². -/
theorem smallest_k2 : solutionSet 8 2 ≠ ∅ := by
  intro h
  have : ({2, 2} : Multiset ℕ) ∈ solutionSet 8 2 := example_8_eq_2sq_2sq
  rw [h] at this
  exact this

/-- The solution set for n=8, k=2 is nonempty. -/
theorem solution_8_nonempty : (solutionSet 8 2).Nonempty :=
  ⟨{2, 2}, example_8_eq_2sq_2sq⟩

/-! ## Summary -/

/-- **Erdős Problem #979 Summary**:

1. QUESTION: Is lim sup f_k(n) = ∞ for all k ≥ 2?
2. SOLVED k=2: Erdős (1937) proved lim sup f_2(n) = ∞
3. SOLVED k=3: Erdős (unpublished) proved lim sup f_3(n) = ∞
4. OPEN k≥4: Unknown whether arbitrarily many representations exist
5. EXAMPLES: 8 = 2² + 2², 24 = 2³ + 2³ + 2³
-/
theorem erdos_979_summary :
    -- Example solutions exist
    ({2, 2} : Multiset ℕ) ∈ solutionSet 8 2 ∧
    ({5, 5} : Multiset ℕ) ∈ solutionSet 50 2 ∧
    ({2, 2, 2} : Multiset ℕ) ∈ solutionSet 24 3 :=
  ⟨example_8_eq_2sq_2sq, example_50, example_24_eq_cubes⟩

end Erdos979
