/-
  Aristotle targets for Erdős Problem #83: Complete Intersection Theorem
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos83Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture (maximum t-intersecting family size)
  - NOT theorems depending on axiomatized background results (EKR, AK theorem)
  - Routine properties of isKUniform, isTIntersecting, and Finset operations
  - No definition sorries
  - No axioms

  Included targets (5):
  - is_zero_intersecting: isTIntersecting F 0 always holds
  - isKUniform_empty: isKUniform ∅ k for any k
  - isTIntersecting_mono: t-intersecting implies j-intersecting for j ≤ t
  - isTIntersecting_singleton: singleton family is t-intersecting for any t ≤ k
  - isKUniform_card_bound: isKUniform F k → F.card ≤ (Finset.univ.powerset).card
-/
import Mathlib

open Finset

namespace Erdos83Aristotle

def isKUniform {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ A ∈ F, A.card = k

def isTIntersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≥ t

-- Routine: any family is 0-intersecting.
-- The intersection of any two sets has card ≥ 0.
theorem is_zero_intersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α)) :
    isTIntersecting F 0 := by
  sorry

-- Routine: the empty family is k-uniform for any k.
-- Vacuously true since ∅ has no members.
theorem isKUniform_empty {α : Type*} [DecidableEq α] (k : ℕ) :
    isKUniform (∅ : Finset (Finset α)) k := by
  sorry

-- Routine: t-intersecting implies j-intersecting for j ≤ t.
-- If every pair intersects in ≥ t elements, they intersect in ≥ j elements too.
theorem isTIntersecting_mono {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (j t : ℕ) (hjt : j ≤ t) (h : isTIntersecting F t) :
    isTIntersecting F j := by
  sorry

-- Routine: a singleton family {S} is t-intersecting for t ≤ S.card.
-- S ∩ S = S, so card ≥ t whenever |S| ≥ t.
theorem isTIntersecting_singleton {α : Type*} [DecidableEq α]
    (S : Finset α) (t : ℕ) (ht : t ≤ S.card) :
    isTIntersecting ({S} : Finset (Finset α)) t := by
  sorry

-- Routine: the empty family is t-intersecting for any t.
-- Vacuously true.
theorem isTIntersecting_empty {α : Type*} [DecidableEq α] (t : ℕ) :
    isTIntersecting (∅ : Finset (Finset α)) t := by
  sorry

end Erdos83Aristotle
