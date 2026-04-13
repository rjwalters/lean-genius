/-
  Aristotle targets for Erdos94 (Distance Multiplicities in Convex Polygons)
  Routine supporting lemmas for automated proof search.
  See Erdos94Problem.lean for the main formalization.

  These lemmas provide building blocks for distance multiplicity analysis:
  - Basic distance properties (positivity, symmetry, distinctness)
  - distanceSet membership and nonemptiness
  - unorderedMultiplicity basic properties
  - Arithmetic helpers for multiplicity bounds
  - Finset helpers for point configurations
-/
import Mathlib

namespace Erdos94.Aristotle

open Finset Real

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-
  ## Section 1: Basic Distance Properties
-/

/-- Distance between distinct points is positive -/
lemma dist_pos_of_ne (p q : Point) (h : p ≠ q) : 0 < dist p q := by
  sorry

/-- Distance is symmetric -/
lemma dist_symm (p q : Point) : dist p q = dist q p := by
  sorry

/-- Distance is zero iff points are equal -/
lemma dist_eq_zero_iff (p q : Point) : dist p q = 0 ↔ p = q := by
  sorry

/-- Any two distinct points have the same positive distance both ways -/
lemma dist_ne_zero_of_ne (p q : Point) (h : p ≠ q) : dist p q ≠ 0 := by
  sorry

/-
  ## Section 2: distanceSet Membership
-/

noncomputable def distanceSet' (P : Finset Point) : Finset ℝ :=
  (P.product P).image (fun pq => dist pq.1 pq.2) |>.filter (· > 0)

/-- Positive distance between points in P belongs to distanceSet -/
lemma mem_distanceSet (P : Finset Point) (p q : Point)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    dist p q ∈ distanceSet' P := by
  sorry

/-- distanceSet is nonempty when P has ≥ 2 distinct elements -/
lemma distanceSet_nonempty (P : Finset Point) (h : P.card ≥ 2) :
    (distanceSet' P).Nonempty := by
  sorry

/-- All elements of distanceSet are positive -/
lemma distanceSet_pos (P : Finset Point) (u : ℝ) (hu : u ∈ distanceSet' P) :
    u > 0 := by
  sorry

/-
  ## Section 3: Point Configuration Helpers
-/

/-- A Finset with card ≥ 2 has two distinct elements -/
lemma has_two_distinct (P : Finset Point) (h : P.card ≥ 2) :
    ∃ p ∈ P, ∃ q ∈ P, p ≠ q := by
  sorry

/-- If P.card ≥ 2 then P.card - 1 ≥ 1 -/
lemma card_sub_one_pos (P : Finset Point) (h : P.card ≥ 2) : P.card - 1 ≥ 1 := by
  sorry

/-- C(n,2) = n*(n-1)/2 for natural numbers -/
lemma choose_two (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by
  sorry

/-
  ## Section 4: Multiplicity Arithmetic
-/

/-- distanceMultiplicity counts ordered pairs, so it is even -/
lemma multiplicity_even_helper (k : ℕ) (h : Even k) : k / 2 * 2 = k := by
  sorry

/-- Sum of multiplicities is at most card squared -/
lemma sum_mult_le_card_sq (n k : ℕ) (h : k ≤ n) : k ≤ n * n := by
  sorry

/-- For n points, C(n,2) ≤ n^2/2 -/
lemma choose_two_le_sq (n : ℕ) : n.choose 2 ≤ n * n / 2 := by
  sorry

/-
  ## Section 5: Convexity Helpers
-/

/-- Erasing a point from a convex hull argument -/
lemma not_mem_convexHull_erase (p : Point) (S : Finset Point) (hp : p ∈ S)
    (hconv : ∀ q ∈ S, q ∉ convexHull ℝ (↑(S.erase q) : Set Point)) :
    p ∉ convexHull ℝ (↑(S.erase p) : Set Point) := by
  sorry

/-- Three collinear points cannot all be vertices of a convex polygon -/
lemma collinear_not_convex (p q r : Point) (S : Finset Point)
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (hcol : Collinear ℝ ({p, q, r} : Set Point)) :
    ¬ (∀ x ∈ S, x ∉ convexHull ℝ (↑(S.erase x) : Set Point)) := by
  sorry

end Erdos94.Aristotle
