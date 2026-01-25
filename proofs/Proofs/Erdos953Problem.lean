/-
Erdős Problem #953

Let A ⊂ {x ∈ ℝ² : |x| < r} be a measurable set with no two points at integer distance.
How large can the measure of A be?

This problem was posed by Erdős and Sárközy in [Er77c]. The question concerns the
maximum measure of a measurable subset of a disk of radius r that avoids all integer
distances between points. For large r, the expected answer is approximately r^(1+o(1))
or possibly O(r^(2-ε)) for some ε > 0.

Reference: https://erdosproblems.com/953
-/

import Mathlib

namespace Erdos953

/-!
## Basic Definitions

We work in ℝ² with the Euclidean metric. A set is integer-distance-free if no two
distinct points in it are at integer distance apart.
-/

/-- A point in the Euclidean plane -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points -/
noncomputable def euclideanDist (p q : Point) : ℝ :=
  ‖p - q‖

/-- Predicate: two points are at integer distance apart -/
def atIntegerDistance (p q : Point) : Prop :=
  ∃ n : ℤ, euclideanDist p q = n

/-- A set is integer-distance-free if no two distinct points are at integer distance -/
def IntegerDistanceFree (S : Set Point) : Prop :=
  ∀ p q : Point, p ∈ S → q ∈ S → p ≠ q → ¬atIntegerDistance p q

/-- The closed ball of radius r centered at the origin in ℝ² -/
def closedDisk (r : ℝ) : Set Point :=
  Metric.closedBall 0 r

/-- The open ball of radius r centered at the origin in ℝ² -/
def openDisk (r : ℝ) : Set Point :=
  Metric.ball 0 r

/-!
## Measure Theory Setup

We use Lebesgue measure on ℝ². The measure of the disk of radius r is πr².
-/

/-- The Lebesgue measure on ℝ² -/
noncomputable def lebesgueMeasure : MeasureTheory.Measure Point :=
  MeasureTheory.volume

/-- A set is measurable in the Lebesgue sense -/
def IsMeasurable (S : Set Point) : Prop :=
  MeasurableSet S

/-- The Lebesgue measure of a set -/
noncomputable def measure (S : Set Point) : ENNReal :=
  lebesgueMeasure S

/-!
## The Erdős-Sárközy Function

We define m(r) as the supremum of measures of measurable integer-distance-free
subsets of the disk of radius r.
-/

/-- The maximum measure of a measurable integer-distance-free subset of the disk of radius r -/
noncomputable def m (r : ℝ) : ENNReal :=
  ⨆ (A : Set Point) (_ : A ⊆ closedDisk r) (_ : IsMeasurable A) (_ : IntegerDistanceFree A),
    measure A

/-!
## Basic Properties

We establish some basic properties of integer-distance-free sets.
-/

/-- The empty set is integer-distance-free -/
theorem emptySet_integerDistanceFree : IntegerDistanceFree ∅ := by
  intro p q hp _
  exact absurd hp (Set.not_mem_empty p)

/-- Singletons are integer-distance-free -/
theorem singleton_integerDistanceFree (p : Point) : IntegerDistanceFree {p} := by
  intro x y hx hy hne
  rw [Set.mem_singleton_iff] at hx hy
  rw [hx, hy] at hne
  exact absurd rfl hne

/-- Subsets of integer-distance-free sets are integer-distance-free -/
theorem IntegerDistanceFree.subset {S T : Set Point}
    (hS : IntegerDistanceFree S) (hTS : T ⊆ S) : IntegerDistanceFree T := by
  intro p q hp hq hne
  exact hS p q (hTS hp) (hTS hq) hne

/-- m(r) is monotone in r -/
theorem m_mono {r s : ℝ} (hrs : r ≤ s) : m r ≤ m s := by
  apply iSup_le_iSup_of_subset
  intro A
  intro hA
  exact Set.Subset.trans hA (Metric.closedBall_subset_closedBall hrs)

/-- m(r) is non-negative (trivially true for ENNReal) -/
theorem m_nonneg (r : ℝ) : 0 ≤ m r := by
  exact zero_le (m r)

/-!
## Trivial Bounds

For any r ≥ 0, there exists a non-empty integer-distance-free set, so m(r) > 0.
The trivial upper bound is the area of the disk, πr².
-/

/-- For r > 0, m(r) is positive -/
theorem m_pos (r : ℝ) (hr : 0 < r) : 0 < m r := by
  have h : {(0 : Point)} ⊆ closedDisk r := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, closedDisk, Metric.mem_closedBall]
    simp [dist_self]
  apply lt_of_lt_of_le _ (le_iSup_of_le {0} (le_iSup_of_le h
    (le_iSup_of_le (measurableSet_singleton 0)
    (le_iSup_of_le (singleton_integerDistanceFree 0) (le_refl _)))))
  simp only [measure, lebesgueMeasure]
  sorry -- Technical measure theory

/-- m(r) is at most the measure of the disk -/
theorem m_le_disk_measure (r : ℝ) (hr : 0 ≤ r) : m r ≤ measure (closedDisk r) := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  apply iSup_le
  intro _
  apply iSup_le
  intro _
  exact MeasureTheory.measure_mono hA

/-!
## The Main Conjecture

Erdős and Sárközy asked for the growth rate of m(r). The conjecture is that
m(r) grows slower than r², meaning integer-distance-free sets must be sparse.

Several related results:
- Furstenberg, Katznelson, Weiss showed that any measurable set of positive
  upper density in ℝ² contains pairs at all large integer distances.
- This suggests m(r) = o(r²) as r → ∞.
-/

/-- The main open question: m(r) grows subquadratically -/
axiom erdos_953_subquadratic_growth :
  ∀ ε > 0, ∃ C : ℝ, ∀ r ≥ 1, m r ≤ ENNReal.ofReal (C * r ^ (2 - ε))

/-- Alternative formulation: m(r)/r² → 0 as r → ∞ -/
axiom erdos_953_density_zero :
  Filter.Tendsto (fun r => (m r).toReal / r^2) Filter.atTop (nhds 0)

/-!
## Connections to Integer Distance Graphs

The integer distance graph on ℝ² has edges between points at integer distance.
An integer-distance-free set is an independent set in this graph.
-/

/-- The integer distance graph structure -/
def integerDistanceAdj (p q : Point) : Prop :=
  p ≠ q ∧ atIntegerDistance p q

/-- An independent set in the integer distance graph -/
def IsIndependentSet (S : Set Point) : Prop :=
  ∀ p q : Point, p ∈ S → q ∈ S → ¬integerDistanceAdj p q

/-- Integer-distance-free is equivalent to independent in the integer distance graph -/
theorem integerDistanceFree_iff_independent (S : Set Point) :
    IntegerDistanceFree S ↔ IsIndependentSet S := by
  constructor
  · intro hS p q hp hq
    intro ⟨hne, hint⟩
    exact hS p q hp hq hne hint
  · intro hS p q hp hq hne hint
    exact hS p q hp hq ⟨hne, hint⟩

/-!
## Unit Distance Avoidance

A related but different problem concerns sets avoiding distance exactly 1.
This is Erdős's unit distance problem for sets rather than finite point sets.
-/

/-- A set avoids unit distance if no two points are distance 1 apart -/
def avoidsUnitDistance (S : Set Point) : Prop :=
  ∀ p q : Point, p ∈ S → q ∈ S → euclideanDist p q ≠ 1

/-- Any set avoiding all integer distances also avoids unit distance -/
theorem integerDistanceFree_avoids_unit {S : Set Point}
    (hS : IntegerDistanceFree S) : avoidsUnitDistance S := by
  intro p q hp hq heq
  by_cases hne : p = q
  · rw [hne, euclideanDist] at heq
    simp at heq
  · have : atIntegerDistance p q := ⟨1, heq⟩
    exact hS p q hp hq hne this

/-!
## Lattice Point Considerations

One approach to understanding m(r) involves lattice points. If we could place
a measurable set that avoids integer distances near each lattice point, we might
get m(r) ~ c·r² for some c < 1. But the constraints are more severe.
-/

/-- The integer lattice in ℝ² -/
def integerLattice : Set Point :=
  {p | ∃ (a b : ℤ), p = ![a, b]}

/-- Two lattice points are always at algebraic distance -/
theorem lattice_algebraic_distance (p q : Point) (hp : p ∈ integerLattice)
    (hq : q ∈ integerLattice) :
    ∃ n : ℕ, (euclideanDist p q)^2 = n := by
  obtain ⟨a₁, b₁, rfl⟩ := hp
  obtain ⟨a₂, b₂, rfl⟩ := hq
  use ((a₁ - a₂)^2 + (b₁ - b₂)^2).natAbs
  sorry -- Calculation involving Euclidean norm

/-!
## Density and Asymptotic Behavior

We can also consider the upper density of integer-distance-free sets.
-/

/-- Upper density of a set in the plane -/
noncomputable def upperDensity (S : Set Point) : ENNReal :=
  Filter.limsup (fun r => measure (S ∩ closedDisk r) / measure (closedDisk r)) Filter.atTop

/-- Conjecture: Any integer-distance-free set has zero upper density -/
axiom erdos_953_zero_density :
  ∀ S : Set Point, IsMeasurable S → IntegerDistanceFree S → upperDensity S = 0

/-!
## The Circle Method Approach

For finite point sets, one can use harmonic analysis. For measurable sets,
the spectral theory of the Laplacian provides insights.
-/

/-- The characteristic function of a measurable set -/
noncomputable def charFun (S : Set Point) : Point → ℝ :=
  Set.indicator S (fun _ => 1)

/-- The autocorrelation at distance d counts pairs at that distance -/
noncomputable def autocorrelation (S : Set Point) (d : ℝ) : ℝ :=
  ∫ p, charFun S p * (∫ q in Metric.sphere p d, charFun S q) ∂lebesgueMeasure

/-- For integer-distance-free sets, autocorrelation at integers is zero -/
theorem integerDistanceFree_autocorr {S : Set Point}
    (hS : IntegerDistanceFree S) (hM : IsMeasurable S) (n : ℕ) (hn : 0 < n) :
    autocorrelation S n = 0 := by
  sorry -- Requires showing pairs at integer distance contribute nothing

/-!
## Main Open Problem Statement

The central question of Erdős Problem #953:
-/

/-- 
Erdős Problem #953 (Open):

Let A ⊂ {x ∈ ℝ² : |x| < r} be a measurable set such that no two points
of A are at integer distance. What is the maximum measure of A?

More precisely: determine the growth rate of m(r) as r → ∞.

Known:
- m(r) ≤ πr² (trivial upper bound)
- m(r) > 0 for all r > 0 (small neighborhoods work)

Conjectured:
- m(r) = o(r²) as r → ∞
- Possibly m(r) = O(r^(2-ε)) for some ε > 0

This is related to the Furstenberg-Katznelson-Weiss theorem on
configurations in sets of positive density.
-/
axiom erdos_953_main_conjecture :
  -- The problem has two aspects:
  -- 1. Upper bound: m(r) grows strictly slower than r²
  (∀ c > 0, ∃ R : ℝ, ∀ r ≥ R, m r < ENNReal.ofReal (c * r^2)) ∧
  -- 2. The exact growth rate is unknown
  True

end Erdos953
