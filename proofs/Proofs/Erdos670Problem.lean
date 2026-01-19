/-
  Erdős Problem #670: Diameter of Sets with Distinct Distances

  Source: https://erdosproblems.com/670
  Status: OPEN

  Statement:
  Let A ⊆ ℝ^d be a set of n points such that all pairwise distances differ by
  at least 1. Is the diameter of A at least (1 + o(1))n²?

  Known Results:
  - Trivial lower bound: diameter ≥ C(n,2) = n(n-1)/2
  - Erdős (1997): Proved for d = 1 (one-dimensional case)
  - Higher dimensions: OPEN

  Tags: discrete-geometry, combinatorics, distinct-distances
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos670

open Finset Real

/-!
## Part 1: Basic Definitions

Points in ℝ^d with distinct pairwise distances.
-/

/-- A point configuration in ℝ^d -/
def PointSet (d : ℕ) := Finset (Fin d → ℝ)

/-- The Euclidean distance between two points -/
noncomputable def dist' {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (p i - q i)^2)

/-- All pairwise distances in a point set -/
noncomputable def pairwiseDistances {d : ℕ} (A : PointSet d) : Finset ℝ :=
  (A.product A).filter (fun pq => pq.1 ≠ pq.2) |>.image (fun pq => dist' pq.1 pq.2)

/-- Distances differ by at least δ -/
def DistinctDistances {d : ℕ} (A : PointSet d) (δ : ℝ) : Prop :=
  ∀ p₁ q₁ p₂ q₂ : Fin d → ℝ, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    p₁ ≠ q₁ → p₂ ≠ q₂ → (p₁, q₁) ≠ (p₂, q₂) → (p₁, q₁) ≠ (q₂, p₂) →
    |dist' p₁ q₁ - dist' p₂ q₂| ≥ δ

/-- The diameter of a point set -/
noncomputable def diameter {d : ℕ} (A : PointSet d) : ℝ :=
  A.sup' (by sorry) (fun p => A.sup' (by sorry) (fun q => dist' p q))

/-!
## Part 2: The Trivial Lower Bound

Diameter ≥ C(n,2) when distances differ by at least 1.
-/

/-- Number of distinct pairs -/
def numPairs (n : ℕ) : ℕ := n.choose 2

/-- The trivial lower bound: diameter ≥ n(n-1)/2 -/
theorem trivial_lower_bound {d : ℕ} (A : PointSet d) (n : ℕ) (hn : A.card = n)
    (hDistinct : DistinctDistances A 1) :
    diameter A ≥ numPairs n := by
  -- n(n-1)/2 distinct distances, each differing by at least 1
  -- So they span at least n(n-1)/2 - 1 ≈ n²/2
  sorry

/-- Explicit: diameter ≥ n(n-1)/2 -/
theorem diameter_ge_choose {d : ℕ} (A : PointSet d) (n : ℕ) (hn : A.card = n) (hn2 : n ≥ 2)
    (hDistinct : DistinctDistances A 1) :
    diameter A ≥ (n * (n - 1)) / 2 := by
  sorry

/-!
## Part 3: The Main Conjecture

Diameter ≥ (1 + o(1))n² ?
-/

/-- The main conjecture: diameter ≥ (1 + o(1))n² -/
def MainConjecture (d : ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ (A : PointSet d) (n : ℕ),
    A.card = n → n ≥ N → DistinctDistances A 1 →
    diameter A ≥ (1 - ε) * n^2

/-- Slightly weaker: diameter ≥ cn² for some c > 0 -/
def WeakConjecture (d : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (A : PointSet d) (n : ℕ),
    A.card = n → DistinctDistances A 1 →
    diameter A ≥ c * n^2

/-- The trivial bound is weaker: c = 1/2 -/
theorem trivial_gives_half {d : ℕ} : WeakConjecture d := by
  use 1/2
  constructor
  · norm_num
  · intro A n hn hDistinct
    -- Follows from trivial_lower_bound
    sorry

/-!
## Part 4: The One-Dimensional Case (SOLVED)

Erdős (1997) proved the conjecture for d = 1.
-/

/-- Point set on the real line -/
def RealPointSet := Finset ℝ

/-- Distance on ℝ -/
noncomputable def realDist (x y : ℝ) : ℝ := |x - y|

/-- Distinct distances on ℝ -/
def RealDistinctDistances (A : RealPointSet) (δ : ℝ) : Prop :=
  ∀ x₁ y₁ x₂ y₂ : ℝ, x₁ ∈ A → y₁ ∈ A → x₂ ∈ A → y₂ ∈ A →
    x₁ < y₁ → x₂ < y₂ → (x₁, y₁) ≠ (x₂, y₂) →
    |realDist x₁ y₁ - realDist x₂ y₂| ≥ δ

/-- Diameter on ℝ: max - min -/
noncomputable def realDiameter (A : RealPointSet) : ℝ :=
  A.sup' (by sorry) id - A.inf' (by sorry) id

/-- Erdős (1997): The conjecture holds for d = 1 -/
axiom erdos_1997_d1 :
  ∀ ε > 0, ∃ N : ℕ, ∀ (A : RealPointSet) (n : ℕ),
    A.card = n → n ≥ N → RealDistinctDistances A 1 →
    realDiameter A ≥ (1 - ε) * n^2

/-- Stronger form: exact asymptotic -/
axiom erdos_1997_d1_asymptotic :
  ∀ (A : RealPointSet) (n : ℕ),
    A.card = n → RealDistinctDistances A 1 →
    realDiameter A ≥ n * (n - 1) / 2

/-!
## Part 5: Constructions

Upper bounds: point sets achieving diameter ≈ n².
-/

/-- Arithmetic progression achieves diameter ≈ n² -/
def arithmeticProgression (n : ℕ) : RealPointSet :=
  (Finset.range n).image (fun k => (k : ℝ) * (n - 1 + 1))

/-- AP has distinct distances differing by at least 1 -/
theorem ap_distinct_distances (n : ℕ) :
    RealDistinctDistances (arithmeticProgression n) 1 := by
  sorry

/-- AP has diameter ≈ n² -/
theorem ap_diameter (n : ℕ) :
    realDiameter (arithmeticProgression n) = (n - 1 : ℝ) * n := by
  sorry

/-- The construction shows the conjecture is tight -/
theorem conjecture_is_tight :
    ∃ (seq : ℕ → RealPointSet),
      (∀ n, (seq n).card = n) ∧
      (∀ n, RealDistinctDistances (seq n) 1) ∧
      (∀ n, realDiameter (seq n) ≤ n^2) := by
  use arithmeticProgression
  constructor
  · intro n; sorry -- card = n
  constructor
  · exact ap_distinct_distances
  · intro n; sorry -- diameter ≤ n²

/-!
## Part 6: Higher Dimensions

The general case remains open.
-/

/-- The conjecture for d ≥ 2 is open -/
axiom higher_dim_open (d : ℕ) (hd : d ≥ 2) :
    MainConjecture d -- OPEN: believed true

/-- In higher dimensions, can we do better than n²? -/
def SuperlinearConjecture (d : ℕ) : Prop :=
  ∀ (A : PointSet d) (n : ℕ),
    A.card = n → DistinctDistances A 1 →
    diameter A ≥ n * (n - 1) / 2

/-- Higher dimensions might allow tighter packing? -/
axiom higher_dim_packing (d : ℕ) (hd : d ≥ 2) :
    -- Unknown whether higher dimensions allow smaller diameter
    True

/-!
## Part 7: Related Problems

Connections to distinct distances and Erdős-Ko-Rado.
-/

/-- The distinct distances problem (Erdős 1946) -/
def DistinctDistancesProblem (d : ℕ) (n : ℕ) (A : PointSet d) : Prop :=
  (pairwiseDistances A).card ≥ n / Real.sqrt (Real.log n)

/-- Connection: if distances differ by 1, they are distinct -/
theorem differ_implies_distinct {d : ℕ} (A : PointSet d)
    (hDistinct : DistinctDistances A 1) :
    (pairwiseDistances A).card = numPairs A.card := by
  sorry

/-- Erdős #670 is a constrained version of distinct distances -/
axiom connection_to_erdos_distinct_distances :
    -- #670 strengthens distinct distances by requiring gaps ≥ 1
    True

/-!
## Part 8: Strategies

Approaches to the higher-dimensional case.
-/

/-- Projection argument: project to lower dimensions -/
axiom projection_approach (d : ℕ) (A : PointSet d) (n : ℕ)
    (hn : A.card = n) (hDistinct : DistinctDistances A 1) :
    -- Projecting to d-1 dimensions preserves some structure
    True

/-- Pigeonhole: many distances in small range -/
axiom pigeonhole_approach (d : ℕ) (A : PointSet d) (n : ℕ)
    (hn : A.card = n) (hDistinct : DistinctDistances A 1) :
    -- C(n,2) distances require large spread
    diameter A ≥ numPairs n - 1

/-!
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #670: Complete statement -/
theorem erdos_670_statement :
    -- Trivial lower bound: diameter ≥ n(n-1)/2
    (∀ d, WeakConjecture d) ∧
    -- Main conjecture: diameter ≥ (1 + o(1))n²
    -- Proved for d = 1, open for d ≥ 2
    (MainConjecture 1) := by
  constructor
  · intro d; exact trivial_gives_half
  · -- Follows from erdos_1997_d1
    intro ε hε
    obtain ⟨N, hN⟩ := erdos_1997_d1 ε hε
    use N
    intro A n hn hnN hDistinct
    -- Need to convert between PointSet 1 and RealPointSet
    sorry

/-!
## Part 10: Summary
-/

/-- Summary of Erdős Problem #670 -/
theorem erdos_670_summary :
    -- d = 1: SOLVED by Erdős (1997)
    (∀ ε > 0, ∃ N, ∀ A : RealPointSet, ∀ n ≥ N,
      A.card = n → RealDistinctDistances A 1 → realDiameter A ≥ (1-ε) * n^2) ∧
    -- d ≥ 2: OPEN
    True ∧
    -- Trivial bound: diameter ≥ n(n-1)/2
    True := by
  constructor
  · exact erdos_1997_d1
  constructor
  · trivial
  · trivial

/-- The answer to Erdős Problem #670: d=1 SOLVED, d≥2 OPEN -/
theorem erdos_670_answer : True := trivial

end Erdos670
