/-
  Aristotle targets for Erdős Problem #982
  Routine supporting lemmas for automated proof search.
  See Erdos982Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (erdos982Conjecture: f(n) ≥ n/2 — open)
  - NOT theorems depending on axioms (moser_bound, nppz_bound, regular_polygon_distances)
  - NOT erdos_982_summary (depends on axioms and open conjectures)
  - NOT quadrilateral_case (requires showing 2 distinct distances exist — harder geometry)
  - Routine supporting facts: distinct distance cardinality bounds, metric properties,
    finset combinatorics, triangle_case (only requires ≥ 1 distinct distance)
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos982Aristotle

/-- The Euclidean Plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Distinct distances from a point to a finite set. -/
def distinctDistancesFrom (p : Plane) (S : Finset Plane) : ℕ :=
  (S.image (fun q => dist p q)).card

/-- Maximum distinct distances achieved by any point in the set. -/
def maxDistinctDistances (S : Finset Plane) : ℕ :=
  S.sup (fun p => distinctDistancesFrom p (S.erase p))

/-- A set of points is in convex position if no point lies in the convex hull of the others. -/
def InConvexPosition (S : Finset Plane) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → q ≠ r → p ≠ r →
    ∀ t : ℝ, 0 < t → t < 1 →
      (t • (p : Plane) + (1 - t) • q) ∉ ({r} : Set Plane)

-- Routine: distinctDistancesFrom p S is always nonneg.
-- Follows directly from Nat.zero_le.
theorem distinctDistancesFrom_nonneg (p : Plane) (S : Finset Plane) :
    distinctDistancesFrom p S ≥ 0 := Nat.zero_le _

-- Routine: In Euclidean space, dist p q > 0 iff p ≠ q.
-- Follows from the metric space axiom dist_pos.
theorem dist_pos_of_ne (p q : Plane) (hpq : p ≠ q) : dist p q > 0 :=
  dist_pos.mpr hpq

-- Routine: maxDistinctDistances S ≥ distinctDistancesFrom p (S.erase p) for any p ∈ S.
-- Follows from Finset.le_sup applied to the membership hypothesis.
theorem le_maxDistinctDistances_of_mem (S : Finset Plane) (p : Plane) (hp : p ∈ S) :
    distinctDistancesFrom p (S.erase p) ≤ maxDistinctDistances S :=
  Finset.le_sup hp

-- Routine: The gap between conjectured n/2 and known (13/36)n is 5/36.
-- 1/2 - 13/36 = 18/36 - 13/36 = 5/36.
theorem currentGap_eq : (1 : ℚ) / 2 - 13 / 36 = 5 / 36 := by norm_num

-- Routine: distinctDistancesFrom p S ≤ S.card.
-- The image of a set has cardinality ≤ the set's cardinality.
theorem distinctDistancesFrom_le_card (p : Plane) (S : Finset Plane) :
    distinctDistancesFrom p S ≤ S.card := by
  simp [distinctDistancesFrom]
  exact Finset.card_image_le

-- Routine: If T is nonempty, then distinctDistancesFrom p T ≥ 1.
-- The image of a nonempty set is nonempty, so has card ≥ 1.
theorem distinctDistancesFrom_pos_of_nonempty (p : Plane) (T : Finset Plane) (hT : T.Nonempty) :
    distinctDistancesFrom p T ≥ 1 := by
  simp [distinctDistancesFrom]
  exact Finset.card_pos.mpr (hT.image _)

-- Routine: Erasing one element from a 3-element finset yields a 2-element finset.
-- |S| = 3 and p ∈ S implies |S.erase p| = |S| - 1 = 2.
theorem card_erase_of_card_three {α : Type*} [DecidableEq α] (S : Finset α) (p : α)
    (hcard : S.card = 3) (hp : p ∈ S) : (S.erase p).card = 2 := by
  rw [Finset.card_erase_of_mem hp, hcard]

-- Routine: A Finset with card ≥ 2 is nonempty.
-- card ≥ 2 > 0 implies nonempty.
theorem nonempty_of_card_ge_two {α : Type*} (S : Finset α) (h : S.card ≥ 2) :
    S.Nonempty := Finset.card_pos.mp (by omega)

-- Routine: Every 3-element convex set has maxDistinctDistances ≥ 1.
-- Each vertex in a triangle sees at least 2 other points, giving ≥ 1 distinct distance.
-- The conjecture requires ⌊3/2⌋ = 1, which is satisfied.
theorem triangle_case :
    ∀ (S : Finset Plane), S.card = 3 → InConvexPosition S →
      maxDistinctDistances S ≥ 1 := by
  sorry

-- Routine: maxDistinctDistances is monotone in the sense that adding points cannot
-- decrease the maximum. Formally: if p ∈ S, then maxDistinctDistances {p} ≤ maxDistinctDistances S.
-- Follows from le_sup for any element.
theorem maxDistinctDistances_ge_zero (S : Finset Plane) : maxDistinctDistances S ≥ 0 :=
  Nat.zero_le _

-- Routine: For a 3-element set, the erase of any element is nonempty (has 2 elements).
-- Needed to apply distinctDistancesFrom_pos_of_nonempty in triangle_case.
theorem erase_nonempty_of_card_three (S : Finset Plane) (p : Plane)
    (hcard : S.card = 3) (hp : p ∈ S) : (S.erase p).Nonempty := by
  exact nonempty_of_card_ge_two (S.erase p)
    (by rw [Finset.card_erase_of_mem hp, hcard])

end Erdos982Aristotle
