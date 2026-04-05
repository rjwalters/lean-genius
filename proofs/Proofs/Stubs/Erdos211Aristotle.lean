/-
  Aristotle targets for Erdős Problem #211: Lines Formed by Points in the Plane
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos211Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (Ω(kn) lines from n points with ≤ n-k collinear)
  - NOT theorems depending on axiomatized incidence bounds (Beck, Szemerédi-Trotter)
  - Routine properties of 2D points, distances, and Finset operations
  - No definition sorries
  - No axioms

  Included targets (5):
  - point_ne_of_coords: (a,b) ≠ (c,d) if a ≠ c or b ≠ d
  - dist_sq_nonneg: distance squared between points is nonneg
  - finset_card_pairs_le: pairs from an n-set has ≤ n*n elements
  - prod_fst_snd: (p.1, p.2) = p for any point p
  - card_filter_le_card: filter count is at most total count
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos211Aristotle

abbrev Point := ℝ × ℝ

-- Routine: two points are distinct if their first coordinates differ.
-- Follows from Prod.ext_iff.
theorem point_ne_of_fst_ne (p q : Point) (h : p.1 ≠ q.1) : p ≠ q := by
  sorry

-- Routine: two points are distinct if their second coordinates differ.
-- Follows from Prod.ext_iff.
theorem point_ne_of_snd_ne (p q : Point) (h : p.2 ≠ q.2) : p ≠ q := by
  sorry

-- Routine: Euclidean distance squared is nonneg.
-- (p.1 - q.1)^2 + (p.2 - q.2)^2 ≥ 0.
theorem dist_sq_nonneg (p q : Point) :
    0 ≤ (p.1 - q.1)^2 + (p.2 - q.2)^2 := by
  sorry

-- Routine: p.fst and p.snd recover p.
-- Definitional equality for product types.
theorem point_eta (p : Point) : (p.1, p.2) = p := by
  sorry

-- Routine: filter count is at most total set card.
-- Finset.card_filter_le.
theorem card_filter_le_card {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] : (s.filter p).card ≤ s.card := by
  sorry

end Erdos211Aristotle
