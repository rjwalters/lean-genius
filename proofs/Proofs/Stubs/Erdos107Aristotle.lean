/-
  Aristotle targets for Erdős Problem #107 (Happy Ending / Erdős–Szekeres)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos107Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open conjecture (f(n) = 2^(n-2) + 1)
  - NOT theorems from axiomatized bounds (ersz, suk, hmpt)
  - Routine finset and convex position facts
  - No definition sorries
  - No axioms

  Included targets (5):
  - isConvexNGon_card: IsConvexNGon n S → S.card = n
  - hasConvexNGon_of_superset: HasConvexNGon n S and S ⊆ T → HasConvexNGon n T
  - f_ge_three: f 3 ≥ 3 (need at least 3 points for a triangle)
  - cardSet_nonempty: (CardSet n).Nonempty for n ≥ 3
  - inGeneralPosition_subset: general position is hereditary under subsets
-/
import Mathlib

namespace Erdos107Aristotle

open Finset

abbrev Point := EuclideanSpace ℝ (Fin 2)

def InGeneralPosition (S : Set Point) : Prop :=
  ∀ p q r : Point, p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r →
    ¬AffineIndependent ℝ ![p, q, r] → False

def IsConvexNGon (n : ℕ) (S : Finset Point) : Prop :=
  S.card = n ∧
  ∀ p ∈ S, p ∉ convexHull ℝ (S.erase p : Set Point)

def HasConvexNGon (n : ℕ) (S : Finset Point) : Prop :=
  ∃ T : Finset Point, T ⊆ S ∧ IsConvexNGon n T

def CardSet (n : ℕ) : Set ℕ :=
  {m : ℕ | ∀ S : Finset Point, S.card = m →
    InGeneralPosition (S : Set Point) → HasConvexNGon n S}

-- Routine: IsConvexNGon implies card = n.
-- By definition of IsConvexNGon.
theorem isConvexNGon_card (n : ℕ) (S : Finset Point) (h : IsConvexNGon n S) :
    S.card = n := by
  sorry

-- Routine: HasConvexNGon is upward-closed.
-- If T ⊆ S has an n-gon and S ⊆ U, then U has an n-gon too.
theorem hasConvexNGon_of_superset (n : ℕ) (S T : Finset Point)
    (hST : S ⊆ T) (hS : HasConvexNGon n S) : HasConvexNGon n T := by
  sorry

-- Routine: InGeneralPosition is hereditary.
-- A subset of a general position set is in general position.
theorem inGeneralPosition_subset (S T : Finset Point)
    (hST : S ⊆ T) (hT : InGeneralPosition (T : Set Point)) :
    InGeneralPosition (S : Set Point) := by
  sorry

-- Routine: HasConvexNGon 1 holds for any nonempty Finset.
-- A single point is trivially a 1-gon.
theorem hasConvexNGon_one (S : Finset Point) (hS : S.Nonempty) :
    HasConvexNGon 1 S := by
  sorry

-- Routine: HasConvexNGon is monotone in n downward.
-- If S contains an n-gon and m ≤ n, it contains an m-gon.
theorem hasConvexNGon_mono (m n : ℕ) (hmn : m ≤ n) (S : Finset Point)
    (h : HasConvexNGon n S) : HasConvexNGon m S := by
  sorry

end Erdos107Aristotle
