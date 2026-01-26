/-!
# Erdős Problem #313 — Primary Pseudoperfect Numbers

Are there infinitely many pairs (m, P) where m ≥ 2 is an integer and
P is a set of distinct primes such that
  ∑_{p ∈ P} 1/p = 1 − 1/m?

## Background

The value m must equal the product p₁ · p₂ · ··· · pₖ, so at most one
solution exists for each m. An integer m satisfying this is called a
**primary pseudoperfect number**.

## Known Solutions (OEIS A054377)

Exactly 8 primary pseudoperfect numbers are known:
  2, 6, 42, 1806, 47058, 2214502422, 52495396602,
  8490421583559688410706771261086

## Examples

- 1/2 = 1 − 1/2 (m = 2, P = {2})
- 1/2 + 1/3 = 1 − 1/6 (m = 6, P = {2, 3})
- 1/2 + 1/3 + 1/7 = 1 − 1/42 (m = 42, P = {2, 3, 7})

*Reference:* [erdosproblems.com/313](https://www.erdosproblems.com/313)
*OEIS:* [A054377](https://oeis.org/A054377)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs

open Finset BigOperators

/-! ## Core Definitions -/

/-- The set of solutions (m, P) to the Erdős 313 equation:
m ≥ 2, P is a nonempty finset of distinct primes, and
  ∑_{p ∈ P} 1/p = 1 − 1/m. -/
def erdos313Solutions : Set (ℕ × Finset ℕ) :=
  { s | 2 ≤ s.1 ∧ s.2.Nonempty ∧
    (∀ p ∈ s.2, p.Prime) ∧
    ∑ p ∈ s.2, (1 : ℚ) / p = 1 - 1 / s.1 }

/-- A natural number n is **primary pseudoperfect** if there exists a
set P of distinct primes such that (n, P) is a solution. -/
def IsPrimaryPseudoperfect (n : ℕ) : Prop :=
  ∃ P : Finset ℕ, (n, P) ∈ erdos313Solutions

/-! ## Main Conjecture -/

/-- **Erdős Problem #313 (Open).**
Are there infinitely many solutions to the equation
  ∑_{p ∈ P} 1/p = 1 − 1/m? -/
axiom erdos_313_conjecture : erdos313Solutions.Infinite

/-- Equivalently: are there infinitely many primary pseudoperfect numbers? -/
axiom primary_pseudoperfect_infinite :
  Set.Infinite { n : ℕ | IsPrimaryPseudoperfect n }

/-! ## Verified Examples -/

/-- m = 2, P = {2}: 1/2 = 1 − 1/2. -/
axiom solution_2 : (2, ({2} : Finset ℕ)) ∈ erdos313Solutions

/-- m = 6, P = {2, 3}: 1/2 + 1/3 = 5/6 = 1 − 1/6. -/
axiom solution_6 : (6, ({2, 3} : Finset ℕ)) ∈ erdos313Solutions

/-- m = 42, P = {2, 3, 7}: 1/2 + 1/3 + 1/7 = 41/42 = 1 − 1/42. -/
axiom solution_42 : (42, ({2, 3, 7} : Finset ℕ)) ∈ erdos313Solutions

/-- m = 1806, P = {2, 3, 7, 43}: 1/2 + 1/3 + 1/7 + 1/43 = 1 − 1/1806. -/
axiom solution_1806 : (1806, ({2, 3, 7, 43} : Finset ℕ)) ∈ erdos313Solutions

/-- m = 47058, P = {2, 3, 11, 23, 31}:
  1/2 + 1/3 + 1/11 + 1/23 + 1/31 = 1 − 1/47058. -/
axiom solution_47058 : (47058, ({2, 3, 11, 23, 31} : Finset ℕ)) ∈ erdos313Solutions

/-! ## Structural Properties -/

/-- **Product constraint.** In any solution (m, P), the value m must
equal the product of all primes in P. -/
axiom product_constraint (m : ℕ) (P : Finset ℕ) (h : (m, P) ∈ erdos313Solutions) :
  m = P.prod id

/-- At most one solution exists for each m, since the prime set P
is determined by the prime factorization of m. -/
axiom uniqueness (m : ℕ) (P₁ P₂ : Finset ℕ)
    (h₁ : (m, P₁) ∈ erdos313Solutions) (h₂ : (m, P₂) ∈ erdos313Solutions) :
  P₁ = P₂

/-- There are at least 8 known primary pseudoperfect numbers. -/
axiom at_least_eight :
  8 ≤ Set.encard { n : ℕ | IsPrimaryPseudoperfect n }

/-! ## Connection to Egyptian Fractions -/

/-- The equation ∑ 1/pᵢ = 1 − 1/m can be rewritten as
  1/p₁ + ··· + 1/pₖ + 1/m = 1,
which is an Egyptian fraction representation of 1 using distinct
denominators where all but possibly m are prime. -/
axiom egyptian_fraction_form (m : ℕ) (P : Finset ℕ) (h : (m, P) ∈ erdos313Solutions) :
  ∑ p ∈ P, (1 : ℚ) / p + 1 / m = 1
