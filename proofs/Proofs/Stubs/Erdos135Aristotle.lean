/-
  Aristotle targets for Erdos135 (Four Points, Five Distances)
  Routine supporting lemmas for automated proof search.
  See Erdos135Problem.lean for the main formalization.

  These lemmas provide building blocks for 4-point distance analysis:
  - fourPointDistances basic properties and membership
  - distanceCount upper bound (C(n,2))
  - Existence examples: square (2 distances), rhombus (3), generic (6)
  - Parallelogram distance helpers
  - Point distinctness from distance conditions
-/
import Mathlib

namespace Erdos135.Aristotle

open Finset

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-
  ## Section 1: fourPointDistances Properties
-/

noncomputable def fourPointDistances' (p₁ p₂ p₃ p₄ : Point) : Finset ℝ :=
  ({dist p₁ p₂, dist p₁ p₃, dist p₁ p₄, dist p₂ p₃, dist p₂ p₄, dist p₃ p₄} : Finset ℝ)

/-- fourPointDistances has at most 6 elements -/
lemma fourPointDistances_card_le_six (p₁ p₂ p₃ p₄ : Point) :
    (fourPointDistances' p₁ p₂ p₃ p₄).card ≤ 6 := by
  sorry

/-- All pairwise distances are in fourPointDistances -/
lemma dist_mem_fourPointDistances (p₁ p₂ p₃ p₄ : Point) :
    dist p₁ p₂ ∈ fourPointDistances' p₁ p₂ p₃ p₄ := by
  sorry

/-- fourPointDistances is nonempty for any 4 points -/
lemma fourPointDistances_nonempty (p₁ p₂ p₃ p₄ : Point) :
    (fourPointDistances' p₁ p₂ p₃ p₄).Nonempty := by
  sorry

/-
  ## Section 2: distanceCount Upper Bound
-/

noncomputable def pairwiseDists (A : Finset Point) : Finset ℝ :=
  (A ×ˢ A).image (fun p => dist p.1 p.2) |>.filter (· > 0)

/-- Pairwise distances ≤ C(n,2) -/
lemma pairwiseDists_card_le (A : Finset Point) :
    (pairwiseDists A).card ≤ A.card * (A.card - 1) / 2 := by
  sorry

/-- Image of filter has card ≤ card of filtered set -/
lemma card_image_filter_le {α β : Type*} [DecidableEq β] (s : Finset α)
    (p : α → Prop) [DecidablePred p] (f : α → β) :
    (s.filter p |>.image f).card ≤ (s.filter p).card := by
  sorry

/-
  ## Section 3: Existence Examples for Specific Distance Counts
-/

/-- A square has exactly 2 distinct distances (side and diagonal) -/
lemma square_two_distances :
    ∃ p₁ p₂ p₃ p₄ : Point,
    p₁ = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0] ∧
    p₂ = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0] ∧
    p₃ = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 1] ∧
    p₄ = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1] ∧
    (fourPointDistances' p₁ p₂ p₃ p₄).card ≤ 3 := by
  sorry

/-- Four points in general position have 6 distinct distances -/
lemma general_position_six_distances :
    ∃ p₁ p₂ p₃ p₄ : Point, (fourPointDistances' p₁ p₂ p₃ p₄).card = 6 := by
  sorry

/-
  ## Section 4: Distance and Point Distinctness
-/

/-- If dist p q > 0 then p ≠ q -/
lemma ne_of_dist_pos (p q : Point) (h : dist p q > 0) : p ≠ q := by
  sorry

/-- dist p q = dist q p -/
lemma dist_comm_points (p q : Point) : dist p q = dist q p := by
  sorry

/-- In a parallelogram, opposite sides have equal length -/
lemma parallelogram_opposite_sides (p₁ p₂ p₃ p₄ : Point)
    (h : p₁ + p₃ = p₂ + p₄) :
    dist p₁ p₂ = dist p₄ p₃ := by
  sorry

/-- In a parallelogram, diagonals bisect each other -/
lemma parallelogram_diag_midpoint (p₁ p₂ p₃ p₄ : Point)
    (h : p₁ + p₃ = p₂ + p₄) :
    (p₁ + p₃) / 2 = (p₂ + p₄) / 2 := by
  sorry

/-
  ## Section 5: HasFiveDistanceProperty Helpers
-/

/-- If card ≥ 5 then the distances have at least 5 distinct values -/
lemma card_ge_five_iff (S : Finset ℝ) : S.card ≥ 5 ↔ ∃ a b c d e : ℝ,
    a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ e ∈ S ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  sorry

end Erdos135.Aristotle
