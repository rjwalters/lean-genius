/-
  Aristotle targets for Erdős Problem #43 (Sidon Sets with Disjoint Differences)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos43Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open conjecture (ErdosProblem43, EqualSizeVariant)
  - NOT theorems depending on axioms (maxSidonSize, barreto_counterexample)
  - Routine Sidon set structural properties
  - No definition sorries
  - No axioms

  Included targets (5):
  - isSidon_empty: empty set is a Sidon set
  - isSidon_subset: Sidon property is downward-closed
  - diffSet_contains_zero: for nonempty A, 0 ∈ diffSet A
  - diffSet_mem: a - b ∈ diffSet A when a, b ∈ A
  - disjointDiff_symm: DisjointDifferences is symmetric
-/
import Mathlib

namespace Erdos43Aristotle

open Finset

def IsSidonSet (A : Finset ℤ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℤ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℤ) = {a₂, b₂}

def diffSet (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 - p.2)

def DisjointDifferences (A B : Finset ℤ) : Prop :=
  ∀ d : ℤ, d ∈ diffSet A → d ∈ diffSet B → d = 0

-- Routine: empty set is a Sidon set.
-- Vacuously, no four elements violate the Sidon condition.
theorem isSidon_empty : IsSidonSet ∅ := by
  sorry

-- Routine: Sidon property is downward-closed.
-- Any subset of a Sidon set is also a Sidon set.
theorem isSidon_subset (A B : Finset ℤ) (hAB : A ⊆ B)
    (hB : IsSidonSet B) : IsSidonSet A := by
  sorry

-- Routine: 0 ∈ diffSet A for nonempty A.
-- For any a ∈ A, a - a = 0 ∈ diffSet A.
theorem diffSet_contains_zero (A : Finset ℤ) (hA : A.Nonempty) : (0 : ℤ) ∈ diffSet A := by
  sorry

-- Routine: a - b ∈ diffSet A when a, b ∈ A.
-- By definition of diffSet as image of product.
theorem diffSet_mem (A : Finset ℤ) (a b : ℤ) (ha : a ∈ A) (hb : b ∈ A) :
    a - b ∈ diffSet A := by
  sorry

-- Routine: DisjointDifferences is symmetric.
-- If A and B have disjoint differences, so do B and A.
theorem disjointDiff_symm (A B : Finset ℤ) (h : DisjointDifferences A B) :
    DisjointDifferences B A := by
  sorry

end Erdos43Aristotle
