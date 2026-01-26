/-!
# Erdős Problem #324: Distinct Polynomial Pair Sums

Does there exist a polynomial f(x) ∈ ℤ[x] such that all the sums
f(a) + f(b) with a < b nonnegative integers are distinct?

It is conjectured that f(x) = x⁵ works. The Lander-Parkin-Selfridge
conjecture would imply f(x) = xⁿ works for all n ≥ 5.

## Status: OPEN

## References
- Erdős and Graham (1980, p. 53)
-/

import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Polynomial

/-!
## Section I: Distinct Pair Sums
-/

/-- The pair sum function: given f ∈ ℤ[X], map (a, b) ↦ f(a) + f(b). -/
noncomputable def pairSumFn (f : ℤ[X]) : ℕ × ℕ → ℤ :=
  fun p => f.eval (p.1 : ℤ) + f.eval (p.2 : ℤ)

/-- The set of ordered pairs (a, b) with a < b. -/
def orderedPairs : Set (ℕ × ℕ) :=
  { p : ℕ × ℕ | p.1 < p.2 }

/-- A polynomial has the distinct pair sum property if f(a) + f(b)
are all distinct for a < b nonneg integers. -/
def HasDistinctPairSums (f : ℤ[X]) : Prop :=
  orderedPairs.InjOn (pairSumFn f)

/-!
## Section II: The Conjecture
-/

/-- **Erdős Problem #324**: Does there exist f ∈ ℤ[X] with the distinct
pair sum property? -/
def ErdosProblem324 : Prop :=
  ∃ f : ℤ[X], HasDistinctPairSums f

/-!
## Section III: The Quintic Conjecture
-/

/-- The specific conjecture that f(x) = x⁵ has distinct pair sums:
a⁵ + b⁵ = c⁵ + d⁵ with a < b and c < d implies (a,b) = (c,d). -/
def QuinticConjecture : Prop :=
  HasDistinctPairSums (X ^ 5 : ℤ[X])

/-- The quintic conjecture implies the main problem. -/
theorem quintic_implies_324 (h : QuinticConjecture) : ErdosProblem324 :=
  ⟨X ^ 5, h⟩

/-!
## Section IV: Power Generalizations
-/

/-- For a given exponent n, the power pair sum property asks whether
aⁿ + bⁿ = cⁿ + dⁿ with a < b and c < d implies (a,b) = (c,d). -/
def PowerPairSumDistinct (n : ℕ) : Prop :=
  HasDistinctPairSums (X ^ n : ℤ[X])

/-- The Lander-Parkin-Selfridge conjecture implies that xⁿ works
for all n ≥ 5. -/
axiom lps_implies_power_distinct :
  (∀ n : ℕ, n ≥ 5 → PowerPairSumDistinct n) → ErdosProblem324

/-- For n = 2, the property fails: 1² + 8² = 4² + 7² = 65. -/
axiom squares_not_distinct : ¬PowerPairSumDistinct 2

/-- For n = 3, the property fails: the Hardy-Ramanujan taxicab
numbers give counterexamples (1³ + 12³ = 9³ + 10³ = 1729). -/
axiom cubes_not_distinct : ¬PowerPairSumDistinct 3

/-- For n = 4, the property fails: there exist equal sums of
two fourth powers (Euler 1772). -/
axiom quartics_not_distinct : ¬PowerPairSumDistinct 4

/-!
## Section V: Lower Degree Impossibility
-/

/-- Linear polynomials cannot have distinct pair sums. -/
axiom linear_not_distinct (a b : ℤ) (ha : a ≠ 0) :
  ¬HasDistinctPairSums (C a * X + C b)

/-- The degree of any polynomial with distinct pair sums must be ≥ 5. -/
axiom min_degree_for_distinct :
  ∀ f : ℤ[X], HasDistinctPairSums f → f.natDegree ≥ 5

/-!
## Section VI: Counting Pair Sums
-/

/-- The number of distinct values of f(a) + f(b) for a < b ≤ N. -/
noncomputable def distinctPairSumCount (f : ℤ[X]) (N : ℕ) : ℕ :=
  (Finset.filter (fun p : ℕ × ℕ => p.1 < p.2)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1))).image
    (fun p => f.eval (p.1 : ℤ) + f.eval (p.2 : ℤ)) |>.card

/-- For distinct pair sums, the count equals C(N+1, 2). -/
axiom distinct_count_eq_binomial (f : ℤ[X]) (hf : HasDistinctPairSums f) (N : ℕ) :
  distinctPairSumCount f N = (N + 1).choose 2
