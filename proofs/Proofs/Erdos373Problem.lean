/-
Erdős Problem #373: Factorials as Products of Factorials

Source: https://erdosproblems.com/373
Status: OPEN (conditionally solved under ABC conjecture)

Statement:
Show that the equation n! = a₁! · a₂! · ... · aₖ! with n-1 > a₁ ≥ a₂ ≥ ... ≥ aₖ ≥ 2
has only finitely many solutions.

Known Results:
- Luca (2007) proved finiteness conditional on ABC conjecture
- Hickerson conjectured the complete list of solutions
- Surányi conjectured 6!7! = 10! is the only two-factor solution
- No solutions with k=2 exist for n ≤ 10^3000 except 10! = 6!7!

References:
- [Er76d] Erdős, "Problems and results on number theoretic properties" (1976)
- [Lu07b] Luca, "On factorials which are products of factorials" (2007)
- [Gu04] Guy, "Unsolved problems in number theory" Problem B23
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat List Set Filter

namespace Erdos373

/-!
## Part I: Core Definitions

A non-trivial factorial product equation n! = a₁! · a₂! · ... · aₖ!
where a₁ ≥ a₂ ≥ ... ≥ aₖ ≥ 2 and a₁ < n - 1.
-/

/-- The product of factorials of a list of natural numbers. -/
def factorialProduct (l : List ℕ) : ℕ :=
  (l.map Nat.factorial).prod

/-- A solution to the factorial product equation.
    (n, [a₁, a₂, ..., aₖ]) is a solution if n! = a₁! · a₂! · ... · aₖ!. -/
def IsSolution (n : ℕ) (l : List ℕ) : Prop :=
  n.factorial = factorialProduct l

/-- A non-trivial solution satisfies:
    1. n! = product of factorials
    2. List is sorted in descending order
    3. Largest term is less than n-1 (rules out trivial solutions)
    4. All terms are at least 2 -/
def IsNontrivialSolution (n : ℕ) (l : List ℕ) : Prop :=
  IsSolution n l ∧
  l.Pairwise (· ≥ ·) ∧
  (l.head? = some (l.headI) → l.headI < n - 1) ∧
  ∀ a ∈ l, 2 ≤ a

/-- The set S of all non-trivial solutions. -/
def S : Set (ℕ × List ℕ) :=
  { p | IsNontrivialSolution p.1 p.2 }

/-!
## Part II: Known Solutions

Hickerson conjectured that these are ALL the non-trivial solutions.
-/

/-- Verify: 9! = 2! · 3! · 3! · 7! -/
theorem solution_9 : Nat.factorial 9 = Nat.factorial 2 * Nat.factorial 3 * Nat.factorial 3 * Nat.factorial 7 := by
  native_decide

/-- Verify: 10! = 6! · 7! (Surányi's famous solution) -/
theorem solution_10_67 : Nat.factorial 10 = Nat.factorial 6 * Nat.factorial 7 := by
  native_decide

/-- Verify: 10! = 3! · 5! · 7! -/
theorem solution_10_357 : Nat.factorial 10 = Nat.factorial 3 * Nat.factorial 5 * Nat.factorial 7 := by
  native_decide

/-- Verify: 16! = 14! · 5! · 2! -/
theorem solution_16 : Nat.factorial 16 = Nat.factorial 14 * Nat.factorial 5 * Nat.factorial 2 := by
  native_decide

/-!
## Part III: The Main Conjecture (OPEN)

The main question: does S have only finitely many elements?
-/

/-- **Erdős Problem #373 (OPEN)**: The set of non-trivial solutions is finite. -/
axiom erdos_373_finiteness : S.Finite

/-!
## Part IV: Conditional Results

Erdős showed the problem reduces to bounds on largest prime factors.
-/

/-- The largest prime factor of n (axiomatized). -/
axiom maxPrimeFactor : ℕ → ℕ

/-- maxPrimeFactor returns the largest prime dividing n, or 0 if n ≤ 1. -/
axiom maxPrimeFactor_spec : ∀ n : ℕ, n > 1 →
  Nat.Prime (maxPrimeFactor n) ∧ maxPrimeFactor n ∣ n ∧
  ∀ p, Nat.Prime p → p ∣ n → p ≤ maxPrimeFactor n

/-- **Erdős's Reduction**: If P(n(n-1)) > 4 log n for large n, then S is finite. -/
axiom erdos_reduction :
  (∀ᶠ (n : ℕ) in atTop, 4 * Real.log (n : ℝ) < (maxPrimeFactor (n * (n - 1)) : ℝ)) →
    S.Finite

/-- **Alternative Reduction**: If P(n(n+1)) / log n → ∞, then S is finite. -/
axiom erdos_reduction_alt :
  Tendsto (fun n => (maxPrimeFactor (n * (n + 1)) : ℝ) / Real.log n) atTop atTop →
    S.Finite

/-!
## Part V: Luca's Theorem (Conditional on ABC)

Florian Luca proved finiteness assuming the ABC conjecture.
-/

/-- The radical of n: product of distinct prime factors (axiomatized). -/
axiom radical : ℕ → ℕ

/-- The ABC conjecture (simplified form). -/
def ABCConjecture : Prop :=
  ∀ ε > 0, ∃ C : ℝ, ∀ a b c : ℕ,
    Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ C * (radical (a * b * c) : ℝ) ^ (1 + ε)

/-- **Luca's Theorem (2007)**: ABC conjecture implies finiteness of S. -/
axiom luca_theorem : ABCConjecture → S.Finite

/-!
## Part VI: Hickerson's Conjecture

The complete classification of all solutions.
-/

/-- Hickerson's conjectured complete list of non-trivial solutions. -/
def hickersonSolutions : Finset (ℕ × List ℕ) :=
  {(9, [7, 3, 3, 2]), (10, [7, 6]), (10, [7, 5, 3]), (16, [14, 5, 2])}

/-- **Hickerson's Conjecture**: The non-trivial solutions are exactly
    9! = 2!3!3!7!, 10! = 6!7!, 10! = 3!5!7!, and 16! = 14!5!2!. -/
axiom hickerson_conjecture :
  S = ↑hickersonSolutions

/-- **Hickerson's Maximum**: The largest n with a solution is n = 16. -/
axiom hickerson_maximum :
  ∀ p ∈ S, p.1 ≤ 16

/-!
## Part VII: Two-Factor Case (Surányi's Conjecture)

The special case n! = a! · b! with a ≤ b < n - 1.
-/

/-- The set of two-factor solutions: n! = a! · b! with proper constraints. -/
def TwoFactorSolutions : Set (ℕ × ℕ × ℕ) :=
  { t | t.1.factorial = t.2.1.factorial * t.2.2.factorial ∧
        2 ≤ t.2.2 ∧ t.2.2 ≤ t.2.1 ∧ t.2.1 + 1 < t.1 }

/-- **Surányi's Conjecture**: The only two-factor solution is 10! = 6! · 7!. -/
axiom suranyi_conjecture :
  TwoFactorSolutions = {(10, 7, 6)}

/-- Known: No two-factor solutions for n ≤ 10^3000 except 10! = 6!7!. -/
axiom computational_verification :
  ∀ t ∈ TwoFactorSolutions, t.1 = 10 ∨ t.1 > 10^3000

/-!
## Part VIII: Bounds on Solutions

Erdős proved that in any solution, a₁ must be close to n.
-/

/-- **Erdős's Bound**: If n! = a₁! · a₂! with n-1 > a₁ ≥ a₂, then a₁ ≥ n - 5 log log n. -/
axiom erdos_bound :
  ∀ n a₁ a₂ : ℕ, n.factorial = a₁.factorial * a₂.factorial →
    a₁ < n - 1 → a₂ ≤ a₁ → 2 ≤ a₂ →
      (a₁ : ℝ) ≥ n - 5 * Real.log (Real.log n)

/-- **Bhat-Ramachandra Improvement**: The constant 5 can be replaced by (1+o(1))/log 2. -/
axiom bhat_ramachandra_bound :
  ∀ ε > 0, ∀ᶠ n in atTop,
    ∀ a₁ a₂ : ℕ, n.factorial = a₁.factorial * a₂.factorial →
      a₁ < n - 1 → a₂ ≤ a₁ → 2 ≤ a₂ →
        (a₁ : ℝ) ≥ n - (1 / Real.log 2 + ε) * Real.log (Real.log n)

/-!
## Summary

**Erdős Problem #373** asks whether the factorial equation n! = a₁!···aₖ!
has only finitely many non-trivial solutions.

**Status**: OPEN (conditionally solved)
- Finiteness proved under ABC conjecture (Luca 2007)
- Would follow from P(n(n-1)) > 4 log n (Erdős)
- Hickerson conjectured exactly 4 solutions exist
- Surányi conjectured only one two-factor solution (10! = 6!7!)
- Computationally verified for n ≤ 10^3000 in two-factor case
-/

theorem erdos_373_summary :
    Nat.factorial 10 = Nat.factorial 6 * Nat.factorial 7 ∧
    Nat.factorial 9 = Nat.factorial 2 * Nat.factorial 3 * Nat.factorial 3 * Nat.factorial 7 ∧
    Nat.factorial 10 = Nat.factorial 3 * Nat.factorial 5 * Nat.factorial 7 ∧
    Nat.factorial 16 = Nat.factorial 14 * Nat.factorial 5 * Nat.factorial 2 := by
  exact ⟨solution_10_67, solution_9, solution_10_357, solution_16⟩

end Erdos373
