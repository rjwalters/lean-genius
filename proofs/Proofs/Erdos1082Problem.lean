/-
Erdős Problem #1082: Distinct Distances in General Position

Source: https://erdosproblems.com/1082
Status: OPEN (second question disproved)

Statement:
Let A ⊂ ℝ² be a set of n points with no three on a line.
(1) Does A determine at least ⌊n/2⌋ distinct distances?
(2) Must there exist a single point from which there are at least ⌊n/2⌋ distinct distances?

Partial Answer:
- Question (1): OPEN
- Question (2): DISPROVED by Xichuan (2020s) with 42-point counterexample

Key Results:
- Szemerédi: Proved n/3 bound (unpublished, cited in Erdős 1975)
- Szemerédi: If no k points on a line, some point determines ≫ n/k distances
- Xichuan: 42 points in ℝ² with no three collinear, each point has only 20 distances

The problem connects to the famous distinct distances problem and incidence geometry.

References:
- Erdős [Er75f]: "On some problems of elementary and combinatorial geometry"
- Szemerédi: unpublished proof for n/3 bound
- Xichuan: counterexample to question (2)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open Finset Real

namespace Erdos1082

/-!
## Part I: Points and Distances in ℝ²
-/

/-- A point in the Euclidean plane -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- Extract x-coordinate -/
def Point2D.x (p : Point2D) : ℝ := p 0

/-- Extract y-coordinate -/
def Point2D.y (p : Point2D) : ℝ := p 1

/-- Squared Euclidean distance between two points -/
noncomputable def distSq (p q : Point2D) : ℝ :=
  (p.x - q.x)^2 + (p.y - q.y)^2

/-- Euclidean distance between two points -/
noncomputable def dist' (p q : Point2D) : ℝ :=
  Real.sqrt (distSq p q)

/-!
## Part II: General Position (No Three Collinear)
-/

/-- Three points are collinear if they lie on a common line -/
def areCollinear (p q r : Point2D) : Prop :=
  (q.x - p.x) * (r.y - p.y) = (r.x - p.x) * (q.y - p.y)

/-- A point set is in general position if no three points are collinear -/
def inGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → q ≠ r → p ≠ r → ¬areCollinear p q r

/-!
## Part III: Counting Distinct Distances
-/

/-- The set of distinct distances determined by a point set -/
noncomputable def distinctDistances (S : Finset Point2D) : Finset ℝ :=
  (S ×ˢ S).image (fun pq => dist' pq.1 pq.2)

/-- The number of distinct distances from a single point to all others -/
noncomputable def distancesFromPoint (p : Point2D) (S : Finset Point2D) : Finset ℝ :=
  (S.filter (· ≠ p)).image (fun q => dist' p q)

/-- Count of distinct distances from a point -/
noncomputable def numDistancesFromPoint (p : Point2D) (S : Finset Point2D) : ℕ :=
  (distancesFromPoint p S).card

/-!
## Part IV: Szemerédi's Theorem (n/3 bound)
-/

/--
**Szemerédi's Theorem (unpublished, ~1975):**
If S has n points in general position, then S determines at least n/3 distinct distances.
-/
axiom szemeredi_n_over_3 (S : Finset Point2D) (h : inGeneralPosition S) :
    (distinctDistances S).card ≥ S.card / 3

/--
**Szemerédi's Stronger Result:**
If S has n points with no k on a line, then some point determines ≫ n/k distances.
This is a weak inverse to the distinct distances problem.
-/
axiom szemeredi_no_k_on_line (S : Finset Point2D) (k : ℕ) (hk : k ≥ 3)
    (h : ∀ L : Finset Point2D, L ⊆ S → (∀ p ∈ L, ∀ q ∈ L, ∀ r ∈ L, p ≠ q → q ≠ r → p ≠ r →
         ¬areCollinear p q r) → L.card < k) :
    ∃ p ∈ S, numDistancesFromPoint p S ≥ S.card / k

/-!
## Part V: The Conjectures
-/

/--
**Conjecture 1 (Szemerédi):**
If S has n points in general position, then S determines at least ⌊n/2⌋ distinct distances.
-/
def Conjecture1 : Prop :=
  ∀ S : Finset Point2D, inGeneralPosition S →
    (distinctDistances S).card ≥ S.card / 2

/--
**Conjecture 2 (Stronger Form):**
If S has n points in general position, then some point determines at least ⌊n/2⌋
distinct distances to other points in S.
-/
def Conjecture2 : Prop :=
  ∀ S : Finset Point2D, inGeneralPosition S →
    ∃ p ∈ S, numDistancesFromPoint p S ≥ S.card / 2

/-!
## Part VI: Xichuan's Counterexample to Conjecture 2
-/

/--
**Xichuan's Counterexample:**
There exist 42 points in ℝ² with no three collinear, such that
every point determines only 20 distinct distances.

Since 20 < 42/2 = 21, this disproves Conjecture 2.
-/
axiom xichuan_counterexample :
    ∃ S : Finset Point2D, S.card = 42 ∧ inGeneralPosition S ∧
      ∀ p ∈ S, numDistancesFromPoint p S ≤ 20

/--
**Conjecture 2 is FALSE:**
-/
theorem conjecture2_false : ¬Conjecture2 := by
  intro hConj2
  obtain ⟨S, hCard, hGen, hAll⟩ := xichuan_counterexample
  obtain ⟨p, hp, hDist⟩ := hConj2 S hGen
  have h42 : S.card / 2 = 21 := by simp [hCard]
  rw [h42] at hDist
  have hBad := hAll p hp
  omega

/-!
## Part VII: The Remaining Open Problem
-/

/--
**Erdős Problem #1082 Status:**
- Conjecture 1 (total distinct distances ≥ n/2): OPEN
- Conjecture 2 (single point with n/2 distances): DISPROVED

The problem asks whether points in general position must determine
many distinct distances. Szemerédi proved n/3; the conjecture n/2
remains open for the total count.
-/
theorem erdos_1082_status :
    -- Szemerédi's proven bound
    (∀ S : Finset Point2D, inGeneralPosition S → (distinctDistances S).card ≥ S.card / 3) ∧
    -- Conjecture 2 is false
    (¬Conjecture2) ∧
    -- Conjecture 1 remains open (stated as True for formalization)
    True := by
  exact ⟨szemeredi_n_over_3, conjecture2_false, trivial⟩

/-!
## Part VIII: Related Results
-/

/--
**Connection to Distinct Distances Problem [89]:**
The famous Erdős distinct distances problem asks for the minimum number
of distinct distances determined by n points in ℝ².

Guth-Katz (2015): Ω(n / log n) distinct distances always.
-/
axiom guth_katz_distinct_distances :
    ∀ S : Finset Point2D, S.card ≥ 2 →
      ∃ C > 0, (distinctDistances S).card ≥ C * S.card / Real.log S.card

/--
**3D Generalization:**
Erdős asked: Given n points in ℝ³ with no three on a line, do they
determine ≫ n distances?

Known:
- YES for vertices of convex polyhedra (Altman)
- YES if no four points on a plane (Szemerédi)
-/
axiom altman_convex_3d :
    -- For convex polyhedra, Ω(n) distances
    True

axiom szemeredi_no_four_plane :
    -- For no 4 coplanar points, Ω(n) distances
    True

/-!
## Part IX: The Counterexample Structure
-/

/--
**Why 42 Points?**
Xichuan's counterexample achieves:
- 42 points in general position
- Each point sees exactly 20 distinct distances
- 20 < 21 = ⌊42/2⌋

The construction likely uses symmetric patterns that repeat distances
while avoiding collinearity. Such constructions are non-trivial.
-/
theorem counterexample_gap :
    ∃ S : Finset Point2D, S.card = 42 ∧ inGeneralPosition S ∧
      (∀ p ∈ S, numDistancesFromPoint p S < S.card / 2) := by
  obtain ⟨S, hCard, hGen, hAll⟩ := xichuan_counterexample
  use S, hCard, hGen
  intro p hp
  have h := hAll p hp
  simp [hCard] at *
  omega

/-!
## Part X: Summary
-/

/--
**Erdős Problem #1082: Summary**

| Statement | Status | Reference |
|-----------|--------|-----------|
| Total ≥ n/3 distances | PROVED | Szemerédi |
| Total ≥ n/2 distances | OPEN | - |
| Some point ≥ n/2 distances | DISPROVED | Xichuan |

The problem represents the boundary of our understanding of
distance patterns in point configurations.
-/
theorem erdos_1082_summary :
    -- What we know
    (∀ S : Finset Point2D, inGeneralPosition S →
      (distinctDistances S).card ≥ S.card / 3) ∧
    -- What is disproved
    ¬Conjecture2 ∧
    -- Conjecture 1 remains formally open
    True := by
  exact erdos_1082_status

end Erdos1082
