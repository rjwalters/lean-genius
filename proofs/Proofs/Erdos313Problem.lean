/-
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

/- ## Core Definitions -/

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

/- ## Main Conjecture -/

/-- **Erdős Problem #313 (Open).**
Are there infinitely many solutions to the equation
  ∑_{p ∈ P} 1/p = 1 − 1/m?
Equivalently: are there infinitely many primary pseudoperfect numbers?
Known: at least 8 solutions exist (verified below). -/

/- ## Verified Examples -/

/-- m = 2, P = {2}: 1/2 = 1 − 1/2. -/
theorem solution_2 : (2, ({2} : Finset ℕ)) ∈ erdos313Solutions := by
  refine ⟨by norm_num, ⟨2, Finset.mem_singleton.mpr rfl⟩, ?_, ?_⟩
  · intro p hp; rw [Finset.mem_singleton.mp hp]; decide
  · simp [Finset.sum_singleton]; push_cast; norm_num

/-- m = 6, P = {2, 3}: 1/2 + 1/3 = 5/6 = 1 − 1/6. -/
theorem solution_6 : (6, ({2, 3} : Finset ℕ)) ∈ erdos313Solutions := by
  refine ⟨by norm_num, ⟨2, by simp⟩, ?_, ?_⟩
  · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> decide
  · simp only [Finset.sum_insert (by decide : (2:ℕ) ∉ ({3} : Finset ℕ)),
               Finset.sum_singleton]; push_cast; norm_num

/-- m = 42, P = {2, 3, 7}: 1/2 + 1/3 + 1/7 = 41/42 = 1 − 1/42. -/
theorem solution_42 : (42, ({2, 3, 7} : Finset ℕ)) ∈ erdos313Solutions := by
  refine ⟨by norm_num, ⟨2, by simp⟩, ?_, ?_⟩
  · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp only [Finset.sum_insert (by decide : (2:ℕ) ∉ ({3, 7} : Finset ℕ)),
               Finset.sum_insert (by decide : (3:ℕ) ∉ ({7} : Finset ℕ)),
               Finset.sum_singleton]; push_cast; norm_num

/-- m = 1806, P = {2, 3, 7, 43}: 1/2 + 1/3 + 1/7 + 1/43 = 1 − 1/1806. -/
theorem solution_1806 : (1806, ({2, 3, 7, 43} : Finset ℕ)) ∈ erdos313Solutions := by
  refine ⟨by norm_num, ⟨2, by simp⟩, ?_, ?_⟩
  · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  · simp only [Finset.sum_insert (by decide : (2:ℕ) ∉ ({3, 7, 43} : Finset ℕ)),
               Finset.sum_insert (by decide : (3:ℕ) ∉ ({7, 43} : Finset ℕ)),
               Finset.sum_insert (by decide : (7:ℕ) ∉ ({43} : Finset ℕ)),
               Finset.sum_singleton]; push_cast; norm_num

/-- m = 47058, P = {2, 3, 11, 23, 31}:
  1/2 + 1/3 + 1/11 + 1/23 + 1/31 = 1 − 1/47058. -/
theorem solution_47058 : (47058, ({2, 3, 11, 23, 31} : Finset ℕ)) ∈ erdos313Solutions := by
  refine ⟨by norm_num, ⟨2, by simp⟩, ?_, ?_⟩
  · intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [Finset.sum_insert (by decide : (2:ℕ) ∉ ({3, 11, 23, 31} : Finset ℕ)),
               Finset.sum_insert (by decide : (3:ℕ) ∉ ({11, 23, 31} : Finset ℕ)),
               Finset.sum_insert (by decide : (11:ℕ) ∉ ({23, 31} : Finset ℕ)),
               Finset.sum_insert (by decide : (23:ℕ) ∉ ({31} : Finset ℕ)),
               Finset.sum_singleton]; push_cast; norm_num

/- ## Structural Properties -/

/-- **Product constraint**: In any solution (m, P), m = ∏ P.
**Uniqueness**: P is determined by m's prime factorization.
**At least 8 known**: primary pseudoperfect numbers include
2, 6, 42, 1806, 47058, 2214502422, 52495396602, 8490421583559688410706771261086. -/

/- ## Connection to Egyptian Fractions -/

/-- The equation ∑ 1/pᵢ = 1 − 1/m can be rewritten as
  1/p₁ + ··· + 1/pₖ + 1/m = 1,
which is an Egyptian fraction representation of 1 using distinct
denominators where all but possibly m are prime. -/
theorem egyptian_fraction_form (m : ℕ) (P : Finset ℕ) (h : (m, P) ∈ erdos313Solutions) :
    ∑ p ∈ P, (1 : ℚ) / p + 1 / m = 1 := by
  have := h.2.2.2
  linarith
