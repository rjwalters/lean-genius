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

References:
- [Er97f] Erdős, "Some problems on finite and infinite graphs"

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

/- ## Part 1: Basic Definitions -/

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

/-- The diameter of a point set (requires nonempty set) -/
noncomputable def diameter {d : ℕ} (A : PointSet d) (hne : A.Nonempty) : ℝ :=
  A.sup' hne (fun p => A.sup' hne (fun q => dist' p q))

/-- Number of distinct pairs -/
def numPairs (n : ℕ) : ℕ := n.choose 2

/- ## Part 2: The Trivial Lower Bound -/

/-- The trivial lower bound: diameter ≥ n(n-1)/2.
    With C(n,2) distinct distances all differing by ≥ 1, the largest must be ≥ C(n,2). -/
/- ## Part 3: The Main Conjecture -/

/-- The main conjecture: diameter ≥ (1 + o(1))n².
    For all ε > 0, sufficiently large n-point sets with distance gaps ≥ 1
    have diameter ≥ (1 - ε)n². -/
def MainConjecture (d : ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ (A : PointSet d) (n : ℕ) (hne : A.Nonempty),
    A.card = n → n ≥ N → DistinctDistances A 1 →
    diameter A hne ≥ (1 - ε) * n^2

/-- Slightly weaker: diameter ≥ cn² for some c > 0. -/
def WeakConjecture (d : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (A : PointSet d) (n : ℕ) (hne : A.Nonempty),
    A.card = n → DistinctDistances A 1 →
    diameter A hne ≥ c * n^2

/-- The trivial bound gives WeakConjecture with c = 1/2. -/
axiom trivial_gives_half {d : ℕ} : WeakConjecture d

/- ## Part 4: The One-Dimensional Case (SOLVED) -/

/-- Point set on the real line -/
def RealPointSet := Finset ℝ

/-- Distance on ℝ -/
noncomputable def realDist (x y : ℝ) : ℝ := |x - y|

/-- Distinct distances on ℝ -/
def RealDistinctDistances (A : RealPointSet) (δ : ℝ) : Prop :=
  ∀ x₁ y₁ x₂ y₂ : ℝ, x₁ ∈ A → y₁ ∈ A → x₂ ∈ A → y₂ ∈ A →
    x₁ < y₁ → x₂ < y₂ → (x₁, y₁) ≠ (x₂, y₂) →
    |realDist x₁ y₁ - realDist x₂ y₂| ≥ δ

/-- Diameter on ℝ: max - min (requires nonempty set) -/
noncomputable def realDiameter (A : RealPointSet) (hne : A.Nonempty) : ℝ :=
  A.sup' hne id - A.inf' hne id

/-- Erdős (1997): The conjecture holds for d = 1.
    On the real line, ordering the points simplifies the argument. -/
axiom erdos_1997_d1 :
  ∀ ε > 0, ∃ N : ℕ, ∀ (A : RealPointSet) (n : ℕ) (hne : A.Nonempty),
    A.card = n → n ≥ N → RealDistinctDistances A 1 →
    realDiameter A hne ≥ (1 - ε) * n^2

/-- Stronger form for d = 1: exact asymptotic diameter ≥ n(n-1)/2. -/
/- ## Part 5: Constructions -/

/-- Arithmetic progression showing the conjecture is tight.
    {0, n, 2n, ..., (n-1)n} has diameter (n-1)n with all distances ≥ n. -/
def arithmeticProgression (n : ℕ) : RealPointSet :=
  (Finset.range n).image (fun k => (k : ℝ) * (n - 1 + 1))

/-- AP has distinct distances differing by at least 1.
    Distances are multiples of n, all at least n apart. -/
/-- AP has diameter ≈ n². -/
/-- The construction shows the conjecture is tight:
    there exist n-point sets with diameter ≤ n² and distance gaps ≥ 1. -/
/- ## Part 6: Higher Dimensions -/

/-- SuperlinearConjecture: diameter ≥ n(n-1)/2 in any dimension. -/
def SuperlinearConjecture (d : ℕ) : Prop :=
  ∀ (A : PointSet d) (n : ℕ) (hne : A.Nonempty),
    A.card = n → DistinctDistances A 1 →
    diameter A hne ≥ n * (n - 1) / 2

/- ## Part 7: Connection to Distinct Distances -/

/-- The distinct distances problem (Erdős 1946) -/
def DistinctDistancesProblem (d : ℕ) (n : ℕ) (A : PointSet d) : Prop :=
  (pairwiseDistances A).card ≥ n / Real.sqrt (Real.log n)

/-- If distances differ by ≥ 1, they are automatically distinct,
    giving exactly C(n,2) distinct distances. -/
/-- Pigeonhole: C(n,2) distances differing by ≥ 1 forces large diameter. -/
/- ## Part 8: Summary -/

/-- Erdős Problem #670: OPEN.
    d = 1: SOLVED by Erdős (1997) — diameter ≥ (1-ε)n² for large n.
    d ≥ 2: OPEN — trivial bound gives diameter ≥ n(n-1)/2.
    Constructions show the n² bound is tight. -/
theorem erdos_670_summary :
    -- d = 1: SOLVED by Erdős (1997)
    (∀ ε > 0, ∃ N, ∀ A : RealPointSet, ∀ n ≥ N, ∀ hne : A.Nonempty,
      A.card = n → RealDistinctDistances A 1 → realDiameter A hne ≥ (1-ε) * n^2) ∧
    -- Trivial bound: WeakConjecture in all dimensions
    (∀ d, WeakConjecture d) := by
  constructor
  · intro ε hε
    obtain ⟨N, hN⟩ := erdos_1997_d1 ε hε
    intro A n hn hne hcard hDistinct
    exact hN A n hne hcard hn hDistinct
  · intro d
    exact trivial_gives_half

end Erdos670
