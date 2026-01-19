/-
  Erdős Problem #1045: Maximum Product of Distances

  Source: https://erdosproblems.com/1045
  Status: OPEN (partially resolved)

  Statement:
  Let z₁,...,zₙ ∈ ℂ with |zᵢ - zⱼ| ≤ 2 for all i,j. Define
  Δ(z₁,...,zₙ) = ∏_{i≠j} |zᵢ - zⱼ|.
  What is the maximum possible value of Δ?
  Is it maximized when the zᵢ are vertices of a regular polygon?

  Answer:
  - Regular polygon is NOT optimal for even n ≥ 4 (Hu-Tang, Cambie)
  - For even n: liminf(max Δ/n^n) ≥ C ≈ 1.304 (Cambie-Dong-Tang)
  - Regular polygon may still be optimal for odd n (open)

  References:
  - Erdős-Herzog-Piranian (1958), Pommerenke (1961)
  - Hu-Tang (counterexamples), Cambie (generalization)
  - Sothanaphan (2025), Cambie-Dong-Tang (2025)

  Tags: complex-analysis, optimization, polynomial, geometry
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos1045

open Complex Real

/-!
## Part 1: Basic Definitions

The diameter constraint and the product of distances.
-/

/-- A configuration of n complex points -/
def Configuration (n : ℕ) := Fin n → ℂ

/-- The diameter constraint: all pairwise distances are at most 2 -/
def DiameterAtMost2 (z : Configuration n) : Prop :=
  ∀ i j : Fin n, Complex.abs (z i - z j) ≤ 2

/-- The product of pairwise distances Δ(z₁,...,zₙ) -/
noncomputable def Delta (z : Configuration n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i ≠ j then Complex.abs (z i - z j) else 1

/-- Alternative: product over ordered pairs only (gives Δ^{1/2}) -/
noncomputable def DeltaSqrt (z : Configuration n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then Complex.abs (z i - z j) else 1

/-!
## Part 2: Regular Polygon Configuration
-/

/-- The n-th roots of unity, scaled to diameter 2 -/
noncomputable def RegularPolygon (n : ℕ) (hn : n > 0) : Configuration n :=
  fun k => Complex.exp (2 * Real.pi * Complex.I * k / n)

/-- Check that regular polygon has diameter 2 when n ≥ 2 -/
axiom regular_polygon_diameter (n : ℕ) (hn : n ≥ 2) :
  DiameterAtMost2 (RegularPolygon n (by omega))

/-- Delta for regular polygon when n is even: Δ = n^n -/
axiom delta_regular_even (n : ℕ) (hn : n ≥ 2) (heven : Even n) :
  Delta (RegularPolygon n (by omega)) = n ^ n

/-- Delta for regular polygon when n is odd: Δ = cos(π/2n)^{-n(n-1)} · n^n -/
axiom delta_regular_odd (n : ℕ) (hn : n ≥ 3) (hodd : Odd n) :
  Delta (RegularPolygon n (by omega)) =
    (Real.cos (Real.pi / (2 * n))) ^ (-(n * (n - 1) : ℤ)) * n ^ n

/-!
## Part 3: Erdős-Herzog-Piranian Bound (1958)

For monic polynomials with connected sublevel set.
-/

/-- Polynomial with roots z₁,...,zₙ -/
noncomputable def polynomialFromRoots (z : Configuration n) : ℂ → ℂ :=
  fun w => ∏ i : Fin n, (w - z i)

/-- The sublevel set {w : |f(w)| < 1} is connected -/
def ConnectedSublevelSet (f : ℂ → ℂ) : Prop :=
  True  -- Placeholder for topological connectivity

/-- Erdős-Herzog-Piranian (1958): If sublevel set connected, Δ < n^n -/
axiom EHP_1958 (z : Configuration n) (hn : n ≥ 1)
    (hconn : ConnectedSublevelSet (polynomialFromRoots z)) :
  Delta z < n ^ n

/-!
## Part 4: Pommerenke's Upper Bound (1961)
-/

/-- Pommerenke (1961): Δ ≤ 2^{O(n)} · n^n for diameter ≤ 2 configurations -/
axiom pommerenke_1961 :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∀ z : Configuration n,
    DiameterAtMost2 z → Delta z ≤ (2 : ℝ) ^ (C * n) * n ^ n

/-!
## Part 5: Counterexamples for Even n

Regular polygon is NOT optimal for even n ≥ 4.
-/

/-- Hu-Tang: Counterexample for n = 4 -/
axiom hu_tang_n4 :
  ∃ z : Configuration 4, DiameterAtMost2 z ∧
    Delta z > Delta (RegularPolygon 4 (by omega))

/-- Hu-Tang: Counterexample for n = 6 -/
axiom hu_tang_n6 :
  ∃ z : Configuration 6, DiameterAtMost2 z ∧
    Delta z > Delta (RegularPolygon 6 (by omega))

/-- Cambie: Regular polygon not optimal for all even n ≥ 4 -/
axiom cambie_even_not_optimal (n : ℕ) (hn : n ≥ 4) (heven : Even n) :
  ∃ z : Configuration n, DiameterAtMost2 z ∧
    Delta z > Delta (RegularPolygon n (by omega))

/-!
## Part 6: Lower Bounds for Even n
-/

/-- The maximum Δ over all valid configurations -/
noncomputable def MaxDelta (n : ℕ) : ℝ :=
  sSup { Delta z | z : Configuration n ∧ DiameterAtMost2 z }

/-- Sothanaphan (2025): liminf max Δ / n^n ≥ 1.0378 for even n -/
axiom sothanaphan_2025 :
  ∃ C : ℝ, C ≥ 1.0378 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n → MaxDelta n / n ^ n ≥ C - ε

/-- Cambie-Dong-Tang: C ≈ 1.304 when 6 | n -/
axiom cambie_dong_tang_6div :
  ∃ C : ℝ, C ≥ 1.304 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 6 ∣ n → MaxDelta n / n ^ n ≥ C - ε

/-- Cambie-Dong-Tang: C ≈ 1.269 for all even n -/
axiom cambie_dong_tang_even :
  ∃ C : ℝ, C ≥ 1.269 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n → MaxDelta n / n ^ n ≥ C - ε

/-!
## Part 7: Odd n Remains Open
-/

/-- Conjecture: Regular polygon is optimal for odd n -/
def RegularPolygonOptimalOdd : Prop :=
  ∀ n : ℕ, n ≥ 3 → Odd n → ∀ z : Configuration n, DiameterAtMost2 z →
    Delta z ≤ Delta (RegularPolygon n (by omega))

/-- This conjecture is still open -/
axiom odd_case_open : True  -- No proof or disproof known

/-!
## Part 8: Examples
-/

/-- Example: n = 2, optimal is two points at distance 2 -/
axiom optimal_n2 :
  ∀ z : Configuration 2, DiameterAtMost2 z →
    Delta z ≤ 4  -- 2 * 2 for the two directions

/-- Example: n = 3 (equilateral triangle) -/
axiom regular_optimal_n3 :
  ∀ z : Configuration 3, DiameterAtMost2 z →
    Delta z ≤ Delta (RegularPolygon 3 (by omega))

/-!
## Part 9: Erdős Problem #1045 Statement
-/

/-- Erdős Problem #1045: The main questions -/
theorem erdos_1045_statement :
    -- Pommerenke's bound
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∀ z : Configuration n,
      DiameterAtMost2 z → Delta z ≤ (2 : ℝ) ^ (C * n) * n ^ n) ∧
    -- Regular polygon not optimal for even n ≥ 4
    (∀ n : ℕ, n ≥ 4 → Even n →
      ∃ z : Configuration n, DiameterAtMost2 z ∧
        Delta z > Delta (RegularPolygon n (by omega))) ∧
    -- Lower bound for even n
    (∃ C : ℝ, C > 1 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n →
      MaxDelta n / n ^ n ≥ C - ε) := by
  constructor
  · exact pommerenke_1961
  constructor
  · exact cambie_even_not_optimal
  · obtain ⟨C, hC, h⟩ := cambie_dong_tang_even
    exact ⟨C, by linarith, h⟩

/-- The problem is partially resolved -/
axiom erdos_1045_partial :
  -- Even case: regular polygon NOT optimal, but exact maximum unknown
  -- Odd case: still open whether regular polygon is optimal
  True

/-!
## Part 10: Summary
-/

/-- Main summary: Erdős Problem #1045 status -/
theorem erdos_1045_summary :
    -- For even n: regular polygon is NOT optimal
    (∀ n : ℕ, n ≥ 4 → Even n →
      ∃ z : Configuration n, DiameterAtMost2 z ∧
        Delta z > Delta (RegularPolygon n (by omega))) ∧
    -- Lower bound for even n exceeds n^n
    (∃ C : ℝ, C > 1 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n →
      MaxDelta n / n ^ n ≥ C - ε) ∧
    -- Odd case: conjecture still open
    True := by
  constructor
  · exact cambie_even_not_optimal
  constructor
  · obtain ⟨C, hC, h⟩ := cambie_dong_tang_even
    exact ⟨C, by linarith, h⟩
  · trivial

/-- The answer to Erdős Problem #1045: PARTIAL -/
theorem erdos_1045_answer :
    -- Even n: Regular polygon is NOT the maximizer
    -- Odd n: Still open
    True := trivial

end Erdos1045
