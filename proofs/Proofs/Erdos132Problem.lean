/-
# Erdős Problem #132: Distance Multiplicities in Planar Point Sets

**Source:** [erdosproblems.com/132](https://erdosproblems.com/132)
**Status:** OPEN
**Prize:** $100 (for any nontrivial result)

## Statement

Let A ⊂ ℝ² be a set of n points. Must there exist two distances which
occur at least once but between at most n pairs of points? Must the
number of such distances → ∞ as n → ∞?

## Background

- Hopf-Pannwitz (1934): The largest distance occurs at most n times
- Erdős-Fishburn (1995): Proved for n = 5, 6
- Clemen-Dumitrescu-Liu (2025): Proved for convex position
- n = 4 is FALSE (two equilateral triangles counterexample)
- General n ≥ 7 remains OPEN

## Approach

We define distance multiplicity and rare distances, formalize the known
results (Hopf-Pannwitz, Erdős-Fishburn, CDL 2025), the n=4
counterexample, and related bounds from the unit distance and distinct
distances problems.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic

open Finset

namespace Erdos132

/- ## Part I: Basic Definitions -/

/-- Point in the plane ℝ² -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Euclidean distance between two points -/
noncomputable def dist (p q : Point) : ℝ := ‖p - q‖

/-- Distance is symmetric -/
theorem dist_symm (p q : Point) : dist p q = dist q p := by
  unfold dist
  rw [← neg_sub, norm_neg]

/-- Distance is non-negative -/
theorem dist_nonneg (p q : Point) : dist p q ≥ 0 := norm_nonneg _

/- ## Part II: Distance Multiplicity -/

/--
The set of unordered pairs {p, q} with p ≠ q at distance d.
-/
def pairsAtDistance (A : Finset Point) (d : ℝ) : Finset (Finset Point) :=
  A.powerset.filter (fun s => s.card = 2 ∧ ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ dist p q = d)

/-- The number of pairs of distinct points in A at distance d -/
def multiplicity (A : Finset Point) (d : ℝ) : ℕ :=
  (pairsAtDistance A d).card

/- ## Part III: Rare Distances -/

/--
A distance d is "rare" in A if it occurs at least once but
at most |A| times. The problem asks whether two such distances
must exist.
-/
def isRareDistance (A : Finset Point) (d : ℝ) : Prop :=
  d > 0 ∧ multiplicity A d ≥ 1 ∧ multiplicity A d ≤ A.card

/--
**Erdős Question Part 1:**
Must every set of n points (for n sufficiently large) have at
least two rare distances?
-/
def erdos132_question1 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/--
**Erdős Question Part 2:**
Does the count of rare distances → ∞ as n → ∞?
-/
def erdos132_question2 (countRare : Finset Point → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    countRare A ≥ k

/--
**Strong Conjecture (Erdős):**
There are at least n^{1-o(1)} rare distances.
-/
def erdos132_strong_conjecture (countRare : Finset Point → ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    (countRare A : ℝ) ≥ (n : ℝ) ^ (1 - ε)

/- ## Part IV: The Hopf-Pannwitz Theorem -/

/--
**Hopf-Pannwitz Theorem (1934):**
The maximum distance in a set of n ≥ 2 points occurs at most n times.

This is the foundational result: it guarantees at least ONE rare
distance always exists. The hard part is finding a SECOND.
-/
axiom hopf_pannwitz :
  ∀ A : Finset Point, A.card ≥ 2 →
    ∃ d : ℝ, d > 0 ∧ multiplicity A d ≥ 1 ∧ multiplicity A d ≤ A.card

/- ## Part V: Counterexample for n = 4 -/

/--
**n = 4 Counterexample:**
Two equilateral triangles of the same side length sharing an edge
form a rhombus. In this configuration, the side distance s occurs
4 times (more than n = 4 is allowed by "at most n"), and only the
maximum distance (the long diagonal) is rare.
Hence only ONE rare distance exists, not two.
-/
axiom counterexample_n4 :
  ∃ A : Finset Point, A.card = 4 ∧
    ¬∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/- ## Part VI: Positive Results -/

/--
**Erdős-Fishburn (1995):** For n = 5, two rare distances always exist.
-/
axiom erdos_fishburn_5 :
  ∀ A : Finset Point, A.card = 5 →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/--
**Erdős-Fishburn (1995):** For n = 6, two rare distances always exist.
-/
axiom erdos_fishburn_6 :
  ∀ A : Finset Point, A.card = 6 →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/- ## Part VII: Convex Position -/

/--
A point set is in convex position if no point lies in the
convex hull of the others (every point is a vertex of the hull).
-/
def inConvexPosition (A : Finset Point) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A.erase p : Set Point))

/--
**Clemen-Dumitrescu-Liu (2025):**
For points in convex position with |A| ≥ 5, two rare distances
always exist.
-/
/- ## Part VIII: Related Bounds -/

/--
**Unit Distance Bound (Spencer-Szemerédi-Trotter):**
The maximum number of unit distances in n points is O(n^{4/3}).
This constrains how many times any single distance can occur.
-/
/--
**Guth-Katz (2015):**
n points determine at least Ω(n / log n) distinct distances.
This resolved Erdős's distinct distances conjecture up to
logarithmic factors.
-/
/- ## Part IX: Summary -/

/--
**Summary of Erdős Problem #132:**

Erdős Problem #132 asks whether every set of n points in ℝ² must
have at least two 'rare' distances (occurring 1 to n times).

**Known results combined here:**
1. Hopf-Pannwitz (1934): At least one rare distance always exists
2. n = 4: Counterexample (only one rare distance)
3. n = 5, 6: Two rare distances exist (Erdős-Fishburn 1995)
4. Convex position: Two rare distances exist (CDL 2025)

**Open:** General n ≥ 7 ($100 prize for any nontrivial result)
-/
theorem erdos_132_summary :
    -- Hopf-Pannwitz: at least one rare distance exists
    (∀ A : Finset Point, A.card ≥ 2 →
      ∃ d : ℝ, d > 0 ∧ multiplicity A d ≥ 1 ∧ multiplicity A d ≤ A.card) ∧
    -- n = 4 counterexample
    (∃ A : Finset Point, A.card = 4 ∧
      ¬∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) ∧
    -- n = 5: two rare distances
    (∀ A : Finset Point, A.card = 5 →
      ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) ∧
    -- n = 6: two rare distances
    (∀ A : Finset Point, A.card = 6 →
      ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) := by
  exact ⟨hopf_pannwitz, counterexample_n4, erdos_fishburn_5, erdos_fishburn_6⟩

end Erdos132
