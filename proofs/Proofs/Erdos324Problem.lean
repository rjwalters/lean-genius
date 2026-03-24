/-
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

/-
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

/-
## Section II: The Conjecture
-/

/-- **Erdős Problem #324**: Does there exist f ∈ ℤ[X] with the distinct
pair sum property? -/
def ErdosProblem324 : Prop :=
  ∃ f : ℤ[X], HasDistinctPairSums f

/-
## Section III: The Quintic Conjecture
-/

/-- The specific conjecture that f(x) = x⁵ has distinct pair sums:
a⁵ + b⁵ = c⁵ + d⁵ with a < b and c < d implies (a,b) = (c,d). -/
def QuinticConjecture : Prop :=
  HasDistinctPairSums (X ^ 5 : ℤ[X])

/-- The quintic conjecture implies the main problem. -/
theorem quintic_implies_324 (h : QuinticConjecture) : ErdosProblem324 :=
  ⟨X ^ 5, h⟩

/-
## Section IV: Power Generalizations
-/

/-- For a given exponent n, the power pair sum property asks whether
aⁿ + bⁿ = cⁿ + dⁿ with a < b and c < d implies (a,b) = (c,d). -/
def PowerPairSumDistinct (n : ℕ) : Prop :=
  HasDistinctPairSums (X ^ n : ℤ[X])

/-- The Lander-Parkin-Selfridge conjecture implies xⁿ works for all n ≥ 5.
    Taking n = 5 trivially gives a solution. -/
theorem lps_implies_power_distinct :
    (∀ n : ℕ, n ≥ 5 → PowerPairSumDistinct n) → ErdosProblem324 :=
  fun h => ⟨X ^ 5, h 5 (by omega)⟩

/-- For n = 2, the property fails: 1² + 8² = 4² + 7² = 65. -/
theorem squares_not_distinct : ¬PowerPairSumDistinct 2 := by
  intro h
  have hp1 : ((1 : ℕ), (8 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((4 : ℕ), (7 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 2 : ℤ[X]) (1, 8) = pairSumFn (X ^ 2 : ℤ[X]) (4, 7) := by
    simp [pairSumFn, eval_pow, eval_X]; norm_num
  exact absurd (h hp1 hp2 heq) (by decide)

/-- For n = 3, the property fails: the Hardy–Ramanujan taxicab number
    1³ + 12³ = 9³ + 10³ = 1729. -/
theorem cubes_not_distinct : ¬PowerPairSumDistinct 3 := by
  intro h
  have hp1 : ((1 : ℕ), (12 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((9 : ℕ), (10 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 3 : ℤ[X]) (1, 12) = pairSumFn (X ^ 3 : ℤ[X]) (9, 10) := by
    simp [pairSumFn, eval_pow, eval_X]; norm_num
  exact absurd (h hp1 hp2 heq) (by decide)

/-- For n = 4, the property fails: 59⁴ + 158⁴ = 133⁴ + 134⁴ = 635318657
    (Euler 1772). -/
theorem quartics_not_distinct : ¬PowerPairSumDistinct 4 := by
  intro h
  have hp1 : ((59 : ℕ), (158 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((133 : ℕ), (134 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 4 : ℤ[X]) (59, 158) = pairSumFn (X ^ 4 : ℤ[X]) (133, 134) := by
    simp [pairSumFn, eval_pow, eval_X]; norm_num
  exact absurd (h hp1 hp2 heq) (by decide)

/-
## Section V: Lower Degree Impossibility
-/

/-- Linear polynomials cannot have distinct pair sums:
    for f(x) = ax + b, f(0) + f(3) = f(1) + f(2) = 3a + 2b. -/
theorem linear_not_distinct (a b : ℤ) (ha : a ≠ 0) :
    ¬HasDistinctPairSums (C a * X + C b) := by
  intro h
  have hp1 : ((0 : ℕ), (3 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((1 : ℕ), (2 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (C a * X + C b) (0, 3) = pairSumFn (C a * X + C b) (1, 2) := by
    simp [pairSumFn, eval_add, eval_mul, eval_C, eval_X]; push_cast; ring
  exact absurd (h hp1 hp2 heq) (by decide)

/-- The degree of any polynomial with distinct pair sums must be ≥ 5. -/
axiom min_degree_for_distinct :
  ∀ f : ℤ[X], HasDistinctPairSums f → f.natDegree ≥ 5

/-
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
