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

  Included targets (5) — all proved:
  - point_ne_of_fst_ne: p.1 ≠ q.1 → p ≠ q (congr_arg Prod.fst)
  - point_ne_of_snd_ne: p.2 ≠ q.2 → p ≠ q (congr_arg Prod.snd)
  - dist_sq_nonneg: 0 ≤ (p.1-q.1)² + (p.2-q.2)² (add_nonneg + sq_nonneg)
  - point_eta: (p.1, p.2) = p (Prod.eta)
  - card_filter_le_card: (s.filter p).card ≤ s.card (Finset.card_filter_le)
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos211Aristotle

abbrev Point := ℝ × ℝ

-- Routine: two points are distinct if their first coordinates differ.
-- Follows from Prod.ext_iff.
theorem point_ne_of_fst_ne (p q : Point) (h : p.1 ≠ q.1) : p ≠ q :=
  fun heq => h (congr_arg Prod.fst heq)

-- Routine: two points are distinct if their second coordinates differ.
-- Follows from Prod.ext_iff.
theorem point_ne_of_snd_ne (p q : Point) (h : p.2 ≠ q.2) : p ≠ q :=
  fun heq => h (congr_arg Prod.snd heq)

-- Routine: Euclidean distance squared is nonneg.
-- (p.1 - q.1)^2 + (p.2 - q.2)^2 ≥ 0.
theorem dist_sq_nonneg (p q : Point) :
    0 ≤ (p.1 - q.1)^2 + (p.2 - q.2)^2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

-- Routine: p.fst and p.snd recover p.
-- Definitional equality for product types.
theorem point_eta (p : Point) : (p.1, p.2) = p :=
  Prod.eta p

-- Routine: filter count is at most total set card.
-- Finset.card_filter_le.
theorem card_filter_le_card {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] : (s.filter p).card ≤ s.card :=
  Finset.card_filter_le s p

end Erdos211Aristotle
