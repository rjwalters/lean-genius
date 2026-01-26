/-!
# Erdős Problem #846 — Non-Trilinear Subsets of the Plane

Let A ⊂ ℝ² be an infinite set such that for some ε > 0, every finite
subset B ⊆ A of size n contains at least εn points with no three collinear.
Must A be the union of finitely many sets, each with no three points collinear?

This is a problem of Erdős, Nešetřil, and Rödl from [Er92b].

Related: Erdős Problem 774, 847.

Reference: https://erdosproblems.com/846
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite
import Mathlib.Tactic

/-! ## Collinearity and Non-Trilinear Sets -/

/-- Three points in ℝ² are collinear if one is an affine combination of the others.
    We use a simplified characterization via the cross product being zero. -/
def AreCollinear (p q r : Fin 2 → ℝ) : Prop :=
  (q 0 - p 0) * (r 1 - p 1) = (r 0 - p 0) * (q 1 - p 1)

/-- A set is non-trilinear if no three distinct points are collinear -/
def NonTrilinear (S : Set (Fin 2 → ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r → ¬AreCollinear p q r

/-! ## The ε-Non-Trilinear Property -/

/-- A set A is ε-non-trilinear if every finite subset B of A contains
    a non-trilinear subset C of size at least ε|B| -/
def IsEpsNonTrilinear (A : Set (Fin 2 → ℝ)) (ε : ℝ) : Prop :=
  ∀ B : Finset (Fin 2 → ℝ), (↑B : Set (Fin 2 → ℝ)) ⊆ A →
    ∃ C : Finset (Fin 2 → ℝ), (↑C : Set (Fin 2 → ℝ)) ⊆ ↑B ∧
      ε * B.card ≤ C.card ∧ NonTrilinear (↑C : Set (Fin 2 → ℝ))

/-- A set is weakly non-trilinear if it is a finite union of
    sets with no three points collinear -/
def IsWeaklyNonTrilinear (A : Set (Fin 2 → ℝ)) : Prop :=
  ∃ n : ℕ, ∃ S : Fin n → Set (Fin 2 → ℝ),
    (∀ i, NonTrilinear (S i)) ∧
    A ⊆ ⋃ i, S i

/-! ## Basic Observations -/

/-- Any non-trilinear set is ε-non-trilinear with ε = 1 -/
axiom nonTrilinear_is_eps_one (A : Set (Fin 2 → ℝ)) (h : NonTrilinear A) :
  IsEpsNonTrilinear A 1

/-- A weakly non-trilinear set (finite union of k non-trilinear sets)
    is ε-non-trilinear with ε = 1/k -/
axiom weaklyNonTrilinear_is_eps (A : Set (Fin 2 → ℝ)) (k : ℕ) (hk : 0 < k)
    (S : Fin k → Set (Fin 2 → ℝ))
    (hS : ∀ i, NonTrilinear (S i))
    (hA : A ⊆ ⋃ i, S i) :
  IsEpsNonTrilinear A (1 / k)

/-- The converse direction: every weakly non-trilinear set has
    the ε-non-trilinear property for some ε > 0 -/
axiom weaklyNonTrilinear_implies_eps (A : Set (Fin 2 → ℝ))
    (h : IsWeaklyNonTrilinear A) :
  ∃ ε : ℝ, ε > 0 ∧ IsEpsNonTrilinear A ε

/-! ## The Erdős–Nešetřil–Rödl Problem -/

/-- Erdős Problem 846 (Erdős–Nešetřil–Rödl): Is every infinite ε-non-trilinear
    subset of ℝ² weakly non-trilinear (a finite union of sets with no three
    collinear)? Open since [Er92b]. -/
axiom ErdosProblem846 :
  ∀ A : Set (Fin 2 → ℝ), A.Infinite →
    ∀ ε : ℝ, ε > 0 → IsEpsNonTrilinear A ε →
      IsWeaklyNonTrilinear A

/-- Contrapositive formulation: if an infinite set A is NOT a finite union
    of non-trilinear sets, then for every ε > 0 there exists a finite
    subset B of A where every subset of size ≥ ε|B| contains three
    collinear points -/
axiom ErdosProblem846_contrapositive :
  ∀ A : Set (Fin 2 → ℝ), A.Infinite →
    ¬IsWeaklyNonTrilinear A →
      ∀ ε : ℝ, ε > 0 → ¬IsEpsNonTrilinear A ε
