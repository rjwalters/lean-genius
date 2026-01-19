/-
Erdős Problem #132: Distance Multiplicities in Planar Point Sets

Source: https://erdosproblems.com/132
Status: OPEN
Prize: $100 (for any nontrivial result)

Statement:
Let A ⊂ ℝ² be a set of n points. Must there exist two distances which occur
at least once but between at most n pairs of points? Must the number of such
distances → ∞ as n → ∞?

Background:
- Asked by Erdős and Pach
- Hopf and Pannwitz (1934): The largest distance occurs at most n times
- This is about "rare distances" - distances that don't occur too often

Key Results:
- n = 4: FALSE (two equilateral triangles of same side length glued together)
- n = 5, 6: TRUE (Erdős-Fishburn 1995)
- Convex position: TRUE (Clemen-Dumitrescu-Liu 2025)
- General n ≥ 7: OPEN

Erdős conjectured there should be at least n^{1-o(1)} such "rare" distances.

References:
- Hopf-Pannwitz (1934): "Aufgabe 167", Jber. Deutsch. Math. Verein.
- Erdős-Fishburn (1995): "Multiplicities of interpoint distances"
- Clemen-Dumitrescu-Liu (2025): "On multiplicities of interpoint distances"
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic

open Finset

namespace Erdos132

/-
## Part I: Basic Definitions
-/

/--
**Point in the Plane:**
We work with points in ℝ².
-/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/--
**Distance Function:**
The Euclidean distance between two points.
-/
noncomputable def dist (p q : Point) : ℝ := ‖p - q‖

/--
**Distance is symmetric:**
-/
theorem dist_symm (p q : Point) : dist p q = dist q p := by
  unfold dist
  rw [← neg_sub, norm_neg]

/--
**Distance is non-negative:**
-/
theorem dist_nonneg (p q : Point) : dist p q ≥ 0 := norm_nonneg _

/-
## Part II: Distance Multiplicity
-/

/--
**Pairs at Distance d:**
The set of unordered pairs {p, q} with p ≠ q at distance d.
-/
def pairsAtDistance (A : Finset Point) (d : ℝ) : Finset (Finset Point) :=
  A.powerset.filter (fun s => s.card = 2 ∧ ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ dist p q = d)

/--
**Distance Multiplicity:**
The number of pairs of distinct points in A at distance d.
-/
def multiplicity (A : Finset Point) (d : ℝ) : ℕ :=
  (pairsAtDistance A d).card

/--
**Distances that Occur:**
The set of distances that appear at least once in A.
-/
noncomputable def distancesOccurring (A : Finset Point) : Set ℝ :=
  {d : ℝ | d > 0 ∧ multiplicity A d ≥ 1}

/-
## Part III: Rare Distances
-/

/--
**Rare Distance:**
A distance d is "rare" in A if it occurs at least once but at most |A| times.
-/
def isRareDistance (A : Finset Point) (d : ℝ) : Prop :=
  d > 0 ∧ multiplicity A d ≥ 1 ∧ multiplicity A d ≤ A.card

/--
**Count of Rare Distances:**
The number of rare distances in the point set A.
-/
noncomputable def countRareDistances (A : Finset Point) : ℕ :=
  sorry -- Would need to count over all occurring distances

/--
**Erdős Question Part 1:**
Must every set of n points have at least two rare distances?
-/
def erdos132_question1 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/--
**Erdős Question Part 2:**
Does the count of rare distances → ∞ as n → ∞?
-/
def erdos132_question2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    countRareDistances A ≥ k

/--
**Strong Conjecture:**
There are at least n^{1-o(1)} rare distances.
-/
def erdos132_strong_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    (countRareDistances A : ℝ) ≥ (n : ℝ) ^ (1 - ε)

/-
## Part IV: The Hopf-Pannwitz Theorem
-/

/--
**Maximum Distance:**
The largest distance between any two points in A.
-/
noncomputable def maxDistance (A : Finset Point) : ℝ :=
  A.sup' sorry (fun p => A.sup' sorry (fun q => dist p q))

/--
**Hopf-Pannwitz Theorem (1934):**
The maximum distance in a set of n points occurs at most n times.

This is the starting point - we know ONE distance is rare (the maximum).
-/
axiom hopf_pannwitz (A : Finset Point) (hA : A.card ≥ 2) :
  multiplicity A (maxDistance A) ≤ A.card

/--
**Corollary: At least one rare distance exists:**
-/
theorem at_least_one_rare (A : Finset Point) (hA : A.card ≥ 2) :
    ∃ d : ℝ, isRareDistance A d := by
  use maxDistance A
  constructor
  · sorry -- maxDistance > 0 for distinct points
  constructor
  · sorry -- maxDistance occurs at least once
  · exact hopf_pannwitz A hA

/-
## Part V: Counterexample for n = 4
-/

/--
**Two Triangles Configuration:**
Two equilateral triangles of the same side length sharing an edge.

    p₁
   /  \
  p₂--p₃
  |    |
  p₄--p₃' (identified with p₃)

Actually: Four points forming a rhombus where both diagonals
equal the side length.
-/
axiom counterexample_n4 :
  ∃ A : Finset Point, A.card = 4 ∧
    ∀ d : ℝ, isRareDistance A d → d = maxDistance A
-- There's only one rare distance (the maximum), not two

/--
**n = 4 is False:**
The statement fails for n = 4.
-/
theorem erdos132_false_for_4 :
    ∃ A : Finset Point, A.card = 4 ∧
      ¬∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂ := by
  obtain ⟨A, hA, hrare⟩ := counterexample_n4
  use A, hA
  intro ⟨d₁, d₂, hne, hr1, hr2⟩
  have h1 := hrare d₁ hr1
  have h2 := hrare d₂ hr2
  rw [h1, h2] at hne
  exact hne rfl

/-
## Part VI: Positive Results
-/

/--
**Erdős-Fishburn (1995): n = 5**
For any 5 points in the plane, there exist two rare distances.
-/
axiom erdos_fishburn_5 :
  ∀ A : Finset Point, A.card = 5 →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/--
**Erdős-Fishburn (1995): n = 6**
For any 6 points in the plane, there exist two rare distances.
-/
axiom erdos_fishburn_6 :
  ∀ A : Finset Point, A.card = 6 →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/-
## Part VII: Convex Position
-/

/--
**Convex Position:**
A point set is in convex position if no point lies in the convex hull
of the others.
-/
def inConvexPosition (A : Finset Point) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A.erase p : Set Point))

/--
**Clemen-Dumitrescu-Liu (2025):**
For points in convex position, two rare distances always exist.
-/
axiom clemen_dumitrescu_liu_convex (A : Finset Point) (hA : A.card ≥ 5)
    (hconv : inConvexPosition A) :
  ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/--
**Not Too Convex:**
A technical condition from CDL25 paper.
-/
axiom notTooConvex : Finset Point → Prop

/--
**CDL (2025): "Not too convex" case**
-/
axiom clemen_dumitrescu_liu_ntc (A : Finset Point) (hA : A.card ≥ 5)
    (hntc : notTooConvex A) :
  ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂

/-
## Part VIII: Related Bounds
-/

/--
**Distinct Distances:**
The number of distinct distances determined by A.
This is related to the Erdős distinct distances problem.
-/
noncomputable def distinctDistances (A : Finset Point) : ℕ := sorry

/--
**Unit Distance Problem:**
The maximum number of unit distances in n points is O(n^{4/3}).
Related bound that constrains how many times any single distance can occur.
-/
axiom unit_distance_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ A : Finset Point, ∀ d : ℝ,
    (multiplicity A d : ℝ) ≤ C * (A.card : ℝ) ^ (4/3 : ℝ)

/--
**Distinct Distances Lower Bound (Guth-Katz 2015):**
n points determine at least Ω(n/log n) distinct distances.
-/
axiom guth_katz_distinct_distances :
  ∃ c : ℝ, c > 0 ∧ ∀ A : Finset Point, A.card ≥ 2 →
    (distinctDistances A : ℝ) ≥ c * (A.card : ℝ) / Real.log (A.card : ℝ)

/-
## Part IX: Why This Is Hard
-/

/--
**The Difficulty:**
1. Hopf-Pannwitz gives ONE rare distance (the maximum)
2. Finding a SECOND rare distance is much harder
3. The counterexample for n=4 shows the problem is subtle
4. Need to understand distance distribution structure

The $100 prize is for "any nontrivial result".
-/
axiom open_problem_difficulty : True

/--
**Conjectured Bound:**
Erdős suggested there might be n^{1-o(1)} rare distances.
This would be a very strong result.
-/
axiom erdos_conjectured_bound :
  -- If true: countRareDistances A ≥ n^{1-o(1)}
  -- The prize is for progress toward this
  True

/-
## Part X: Summary
-/

/--
**Summary of Known Results:**
-/
theorem erdos_132_summary :
    -- Hopf-Pannwitz: max distance is rare
    (∀ A : Finset Point, A.card ≥ 2 → multiplicity A (maxDistance A) ≤ A.card) ∧
    -- n = 4: Counterexample exists
    (∃ A : Finset Point, A.card = 4 ∧
      ¬∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) ∧
    -- n = 5, 6: Two rare distances exist
    (∀ A : Finset Point, A.card = 5 →
      ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) ∧
    (∀ A : Finset Point, A.card = 6 →
      ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) ∧
    -- Convex position: Two rare distances exist
    (∀ A : Finset Point, A.card ≥ 5 → inConvexPosition A →
      ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ isRareDistance A d₁ ∧ isRareDistance A d₂) := by
  constructor
  · exact hopf_pannwitz
  constructor
  · exact erdos132_false_for_4
  constructor
  · exact erdos_fishburn_5
  constructor
  · exact erdos_fishburn_6
  · intro A hA hconv
    exact clemen_dumitrescu_liu_convex A hA hconv

/--
**Erdős Problem #132: OPEN**

Must every set of n ≥ 5 points in ℝ² have at least two rare distances?
(where a rare distance occurs between 1 and n pairs)

- TRUE for n = 5, 6 (Erdős-Fishburn)
- TRUE for convex position (Clemen-Dumitrescu-Liu)
- OPEN for general n ≥ 7
-/
theorem erdos_132 : True := trivial

end Erdos132
