/-
# Erdős Problem #422 — Hofstadter-Type Recursive Sequence

Define f(1) = f(2) = 1 and for n > 2:
  f(n) = f(n − f(n−1)) + f(n − f(n−2))

Questions:
1. Is f(n) well-defined for all n?
2. Does f miss infinitely many integers?
3. Is f surjective?
4. What is the growth rate of f?

The sequence begins: 1, 1, 2, 3, 3, 4, ...

Status: OPEN
Reference: https://erdosproblems.com/422
OEIS: A005185
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/- ## Computable Definition -/

/-- Compute the Hofstadter sequence values f(0), f(1), ..., f(n) as a list.
    f(0) = 0 (sentinel), f(1) = f(2) = 1, and for k ≥ 3:
    f(k) = f(k - f(k-1)) + f(k - f(k-2)).
    Out-of-bounds lookups default to 0, making this total. -/
def hofstadterFList : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 1]
  | n + 3 =>
      let prev := hofstadterFList (n + 2)
      let k := n + 3
      let fk1 := prev.getD (k - 1) 0
      let fk2 := prev.getD (k - 2) 0
      let v1 := prev.getD (k - fk1) 0
      let v2 := prev.getD (k - fk2) 0
      prev ++ [v1 + v2]

/-- The Hofstadter sequence from Erdős Problem #422 (OEIS A005185).
    Total computable function agreeing with the recursion when well-defined. -/
def hofstadterF (n : ℕ) : ℕ := (hofstadterFList n).getD n 0

/- ## Proved Initial Values -/

theorem hofstadterF_one : hofstadterF 1 = 1 := by native_decide
theorem hofstadterF_two : hofstadterF 2 = 1 := by native_decide
theorem hofstadterF_three : hofstadterF 3 = 2 := by native_decide
theorem hofstadterF_four : hofstadterF 4 = 3 := by native_decide
theorem hofstadterF_five : hofstadterF 5 = 3 := by native_decide
theorem hofstadterF_six : hofstadterF 6 = 4 := by native_decide

/-- The first six values of the Hofstadter sequence match OEIS A005185.
    Proved from the computable definition. -/
theorem initial_values :
    hofstadterF 1 = 1 ∧ hofstadterF 2 = 1 ∧
    hofstadterF 3 = 2 ∧ hofstadterF 4 = 3 ∧
    hofstadterF 5 = 3 ∧ hofstadterF 6 = 4 :=
  ⟨hofstadterF_one, hofstadterF_two, hofstadterF_three,
   hofstadterF_four, hofstadterF_five, hofstadterF_six⟩

/- ## Well-Definedness -/

/-- The recursion is well-defined at index k if the recursive lookups
    stay within the previously computed range. -/
def WellDefinedAt (k : ℕ) : Prop :=
  k ≥ 3 → hofstadterF (k - 1) ≥ 1 ∧ hofstadterF (k - 1) < k ∧
           hofstadterF (k - 2) ≥ 1 ∧ hofstadterF (k - 2) < k

/-- The sequence is well-defined up to index n. -/
def IsWellDefined (n : ℕ) : Prop :=
  ∀ k, k ≤ n → WellDefinedAt k

/- ## Open Questions -/

/-- **Well-Definedness** (OPEN): Is the recursion well-defined for all n?
    It is not known whether the recursive indices always stay in bounds. -/
/-- **Missing Integers** (OPEN): Does f miss infinitely many positive integers? -/
/-- **Non-Surjectivity** (OPEN): Is f non-surjective on positive integers? -/
/-- **Growth Rate** (OPEN): f(n) grows at most linearly. -/
/- ## Observations -/

/- **Hofstadter Origin**: the sequence was proposed by Hofstadter and
    communicated to Erdős. It appears in Erdős–Graham (1980). -/

/- **Self-Referential Recursion**: f(n) depends on f at points
    determined by earlier values of f itself. This self-referential
    nature makes analysis extremely difficult. -/

/- **Eventually Constant?**: it is open whether f becomes constant. -/
