/-!
# Erdős Problem #469: Primitive Pseudoperfect Numbers

A positive integer n is pseudoperfect if it can be written as a sum of
distinct proper divisors. It is primitive pseudoperfect if n is
pseudoperfect but no proper divisor m | n (m < n) is pseudoperfect.

Let A be the set of primitive pseudoperfect numbers (OEIS A006036).
Does Σ_{n ∈ A} 1/n converge?

Known members of A include: 6, 20, 28, 88, 104, 272, 304, 350, ...

Status: OPEN.

Reference: https://erdosproblems.com/469
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Divisors

/-! ## Definitions -/

/-- n is pseudoperfect: n can be written as a sum of distinct proper
    divisors of n. -/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ S.sum id = n

/-- n is primitive pseudoperfect: n is pseudoperfect, but no proper
    divisor of n (less than n) is pseudoperfect. -/
def IsPrimitivePseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ IsPseudoperfect n ∧
  ∀ m : ℕ, m < n → m ∣ n → ¬IsPseudoperfect m

/-- The set A of primitive pseudoperfect numbers. -/
def primitivePseudoperfectSet : Set ℕ :=
  {n : ℕ | IsPrimitivePseudoperfect n}

/-! ## Known Results -/

/-- 6 is pseudoperfect: 6 = 1 + 2 + 3 and 1, 2, 3 are proper divisors. -/
axiom six_pseudoperfect : IsPseudoperfect 6

/-- 6 is the smallest perfect number, and it is primitive pseudoperfect
    since no proper divisor of 6 (1, 2, 3) is pseudoperfect. -/
axiom six_primitive : IsPrimitivePseudoperfect 6

/-- Every perfect number is pseudoperfect (since σ(n) = 2n implies
    the proper divisors sum to n). -/
axiom perfect_is_pseudoperfect (n : ℕ) (hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) : IsPseudoperfect n

/-- There are infinitely many primitive pseudoperfect numbers. -/
axiom infinitely_many_primitive :
  Set.Infinite primitivePseudoperfectSet

/-- Every multiple of a pseudoperfect number is pseudoperfect. -/
axiom multiple_of_pseudoperfect (n m : ℕ) (hn : IsPseudoperfect n)
    (hm : 0 < m) : IsPseudoperfect (n * m)

/-! ## The Open Question -/

/-- Erdős Problem #469: Does the sum of reciprocals of primitive
    pseudoperfect numbers converge?
    Σ_{n ∈ A} 1/n < ∞ ? -/
axiom erdos_469_convergence :
  ∃ B : ℝ, 0 < B ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, IsPrimitivePseudoperfect n) →
      (S.sum (fun n => (1 : ℝ) / n)) ≤ B
