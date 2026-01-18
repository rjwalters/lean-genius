/-
  Erdős Problem #604: The Pinned Distance Problem

  Source: https://erdosproblems.com/604
  Status: OPEN
  Prize: $500

  Statement:
  Given n distinct points A ⊂ ℝ², must there exist a point x ∈ A
  (called the "pinned point") such that the number of distinct distances
  from x to other points in A is at least n^(1-o(1))? Even n/√(log n)?

  This is the "pinned" version of the Erdős distinct distances problem.
  Rather than counting all pairwise distances, we ask: does some point
  see many different distances to other points in the set?

  Context:
  - This is a stronger form of Erdős Problem #89 (distinct distances)
  - The integer lattice {1,...,√n} × {1,...,√n} shows n/√(log n) would be optimal
  - Best known bound: Katz-Tardos proved exponent c ≈ 0.864
  - The full conjecture (exponent 1-o(1)) remains OPEN

  Historical Note:
  Erdős conjectured that the sum of distinct distances over all pinned points
  satisfies Σ_x |{d(x,y) : y ∈ A}| >> n²/√(log n). He initially believed this
  matched the total distinct distance count, but Harborth disproved this.

  Prize Ambiguity:
  It is unclear whether the $500 prize applies to finding one point with
  many distinct distances, or showing >> n such points exist.
-/

import Mathlib

open Finset Real Set

/-! ## Basic Definitions for Planar Point Sets -/

/-- The Euclidean distance between two points in ℝ² -/
noncomputable def euclideanDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

/-- The set of distinct distances from a point x to all other points in A -/
noncomputable def pinnedDistances (x : ℝ × ℝ) (A : Finset (ℝ × ℝ)) : Finset ℝ :=
  (A.filter (· ≠ x)).image (euclideanDist x)

/-- The number of distinct distances from x to points in A -/
noncomputable def pinnedDistanceCount (x : ℝ × ℝ) (A : Finset (ℝ × ℝ)) : ℕ :=
  (pinnedDistances x A).card

/-- The maximum number of distinct pinned distances over all points in A -/
noncomputable def maxPinnedDistances (A : Finset (ℝ × ℝ)) : ℕ :=
  A.sup' (by sorry) (fun x => pinnedDistanceCount x A)

/-! ## The Pinned Distance Conjecture -/

/-- Erdős Problem #604: The weak pinned distance conjecture.
    Every n-point set has a point with at least n^(1-ε) distinct distances
    for any ε > 0 and sufficiently large n. -/
def pinnedDistanceConjecture : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ A : Finset (ℝ × ℝ), A.card ≥ N₀ →
    ∃ x ∈ A, (pinnedDistanceCount x A : ℝ) ≥ (A.card : ℝ) ^ (1 - ε)

/-- The strong form: pinned distances grow like n/√(log n) -/
def strongPinnedDistanceConjecture : Prop :=
  ∃ c > 0, ∀ A : Finset (ℝ × ℝ), A.card ≥ 2 →
    ∃ x ∈ A, (pinnedDistanceCount x A : ℝ) ≥ c * (A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ))

/-! ## Katz-Tardos Bound -/

/-- The Katz-Tardos exponent: c = (48 - 14e) / (55 - 16e) ≈ 0.864137 -/
noncomputable def katzTardosExponent : ℝ :=
  (48 - 14 * Real.exp 1) / (55 - 16 * Real.exp 1)

/-- The Katz-Tardos theorem (2004): The maximum pinned distance count
    is at least n^c where c ≈ 0.864. This is the best known lower bound. -/
theorem katzTardos_bound (A : Finset (ℝ × ℝ)) (hA : A.card ≥ 2) :
    ∃ x ∈ A, ∃ c > 0, (pinnedDistanceCount x A : ℝ) ≥ c * (A.card : ℝ) ^ katzTardosExponent := by
  sorry

/-! ## Related Bounds and Variants -/

/-- Basic lower bound: Every point sees at least 1 distinct distance (trivial) -/
theorem pinnedDistance_pos (A : Finset (ℝ × ℝ)) (x : ℝ × ℝ) (hx : x ∈ A)
    (hA : A.card ≥ 2) : pinnedDistanceCount x A ≥ 1 := by
  sorry

/-- Upper bound: No point can see more than n-1 distinct distances -/
theorem pinnedDistance_le (A : Finset (ℝ × ℝ)) (x : ℝ × ℝ) :
    pinnedDistanceCount x A ≤ A.card - 1 := by
  unfold pinnedDistanceCount pinnedDistances
  calc (A.filter (· ≠ x)).image (euclideanDist x) |>.card
      ≤ (A.filter (· ≠ x)).card := Finset.card_image_le
    _ ≤ A.card := Finset.card_filter_le A _
    _ ≤ A.card - 0 := by omega
    _ ≤ A.card - 1 := by sorry

/-- The integer lattice achieves the conjectured upper bound construction -/
theorem integerLattice_pinnedDistances (n : ℕ) (hn : n ≥ 2) :
    ∃ A : Finset (ℝ × ℝ), A.card = n ∧
      ∀ x ∈ A, (pinnedDistanceCount x A : ℝ) ≤ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  sorry

/-! ## Sum of Pinned Distances -/

/-- Total pinned distance count summed over all points -/
noncomputable def totalPinnedDistanceSum (A : Finset (ℝ × ℝ)) : ℕ :=
  A.sum (fun x => pinnedDistanceCount x A)

/-- Erdős's conjecture on the sum: Σ_x d(x) >> n²/√(log n) -/
def pinnedDistanceSumConjecture : Prop :=
  ∃ c > 0, ∀ A : Finset (ℝ × ℝ), A.card ≥ 2 →
    (totalPinnedDistanceSum A : ℝ) ≥ c * (A.card : ℝ)^2 / Real.sqrt (Real.log (A.card : ℝ))

/-! ## Connection to General Distinct Distances -/

/-- The set of all pairwise distinct distances in A -/
noncomputable def allDistinctDistances (A : Finset (ℝ × ℝ)) : Finset ℝ :=
  (A.product A).filter (fun (p, q) => p ≠ q) |>.image (fun (p, q) => euclideanDist p q)

/-- Pinned distances are a subset of all distinct distances -/
theorem pinnedDistances_subset_all (A : Finset (ℝ × ℝ)) (x : ℝ × ℝ) (hx : x ∈ A) :
    pinnedDistances x A ⊆ allDistinctDistances A := by
  intro d hd
  unfold pinnedDistances at hd
  simp only [mem_image, mem_filter] at hd
  obtain ⟨y, ⟨hy_mem, hy_ne⟩, hy_dist⟩ := hd
  unfold allDistinctDistances
  simp only [mem_image, mem_filter, mem_product]
  exact ⟨(x, y), ⟨⟨hx, hy_mem⟩, hy_ne⟩, hy_dist⟩

/-! ## Main Open Problem Statement -/

/-- Erdős Problem #604: OPEN
    The pinned distance conjecture remains unproven.
    The $500 prize is for proving the exponent approaches 1. -/
theorem erdos_604_open : pinnedDistanceConjecture ↔ pinnedDistanceConjecture := by
  rfl

#check pinnedDistanceConjecture
#check katzTardos_bound
#check erdos_604_open
