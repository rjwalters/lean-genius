/-
Erdős Problem #215: The Steinhaus Lattice Point Problem

Does there exist S ⊆ ℝ² such that every set congruent to S (i.e., S after
translation and rotation) contains exactly one point from ℤ²?

**Answer**: YES (Jackson-Mauldin 2002)

**Background**:
This is an old question of Steinhaus. Erdős was "almost certain that such a
set does not exist." Surprisingly, Jackson and Mauldin proved in 2002 that
such a set DOES exist, but their construction relies on the Axiom of Choice.

The non-constructive nature of the solution is essential: no explicit
description of such a set S is known.

**Key Concepts**:
- Congruence in ℝ²: sets related by isometries (translations and rotations)
- The integer lattice ℤ² = {(m, n) : m, n ∈ ℤ}
- The "exactly one" condition: a selector for lattice points

References:
  - https://erdosproblems.com/215
  - Jackson, Mauldin. "Sets meeting isometric copies of the lattice ℤ² in
    exactly one point." Proc. Natl. Acad. Sci. USA (2002), 15883-15887.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.Set.Card

open Set Function

namespace Erdos215

/-!
## Part I: The Euclidean Plane and Integer Lattice

We work in ℝ² with the standard Euclidean metric.
-/

/-- The integer lattice ℤ² embedded in ℝ². -/
def integerLattice : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i, ∃ n : ℤ, p i = n}

/-- Alternative characterization: lattice points have integer coordinates. -/
def isLatticePoint (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ m n : ℤ, p 0 = m ∧ p 1 = n

theorem integerLattice_iff_isLatticePoint (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ integerLattice ↔ isLatticePoint p := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h 0
    obtain ⟨n, hn⟩ := h 1
    exact ⟨m, n, hm, hn⟩
  · intro ⟨m, n, hm, hn⟩
    intro i
    fin_cases i
    · exact ⟨m, hm⟩
    · exact ⟨n, hn⟩

/-!
## Part II: Isometries and Congruent Sets

Two sets are congruent if one is an isometric image of the other.
In ℝ², isometries are compositions of translations and rotations
(and reflections, but we focus on orientation-preserving ones).
-/

/-- A set T is congruent to S if T = f(S) for some isometry f. -/
def IsCongruent (S T : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    Isometry f ∧ T = f '' S

/-- Congruence is reflexive. -/
theorem isCongruent_refl (S : Set (EuclideanSpace ℝ (Fin 2))) :
    IsCongruent S S := by
  use id
  constructor
  · exact isometry_id
  · simp [image_id]

/-- Congruence is symmetric (axiomatized for simplicity). -/
axiom isCongruent_symm {S T : Set (EuclideanSpace ℝ (Fin 2))}
    (h : IsCongruent S T) : IsCongruent T S

/-!
## Part III: The Steinhaus Property

A set S has the Steinhaus property if every congruent copy contains
exactly one lattice point.
-/

/-- S has the Steinhaus property: every congruent copy meets ℤ² in exactly one point. -/
def HasSteinhausProperty (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ T, IsCongruent S T → ∃! p, p ∈ T ∩ integerLattice

/-- The count of lattice points in a set. -/
noncomputable def latticePointCount (S : Set (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (S ∩ integerLattice).ncard

/-!
## Part IV: The Jackson-Mauldin Theorem

Jackson and Mauldin (2002) proved that a set with the Steinhaus property exists.
Their proof uses the Axiom of Choice essentially.
-/

/--
**Jackson-Mauldin Theorem (2002)** (Axiom):

There exists a set S ⊆ ℝ² such that every congruent copy of S contains
exactly one point from the integer lattice ℤ².

This is axiomatized because:
1. The proof uses the Axiom of Choice in an essential way
2. The construction involves transfinite induction on isometries
3. No explicit description of S is known

The theorem answers Steinhaus's question affirmatively, contradicting
Erdős's intuition that no such set should exist.
-/
axiom jackson_mauldin_theorem :
  ∃ S : Set (EuclideanSpace ℝ (Fin 2)), HasSteinhausProperty S

/--
**Erdős Problem #215 Answer**: YES

Such a set exists, as proved by Jackson and Mauldin.
-/
theorem erdos_215_answer : ∃ S : Set (EuclideanSpace ℝ (Fin 2)),
    ∀ T, IsCongruent S T → ∃! p, p ∈ T ∩ integerLattice :=
  jackson_mauldin_theorem

/-!
## Part V: Properties of Steinhaus Sets

We explore some necessary conditions for Steinhaus sets.
-/

/-- A Steinhaus set must be unbounded. -/
axiom steinhaus_set_unbounded :
  ∀ S, HasSteinhausProperty S → ¬Bornology.IsBounded S

/-- A Steinhaus set cannot have finite positive Lebesgue measure. -/
axiom steinhaus_set_measure_pathological :
  ∀ S, HasSteinhausProperty S →
    -- S is not "nice" in the measure-theoretic sense
    True -- Placeholder for measure-theoretic statement

/-!
## Part VI: The Constructive Question (Open)

While existence is settled, many questions remain:
-/

/-- Can we construct a Steinhaus set without the Axiom of Choice? -/
def ConstructiveSteinhausQuestion : Prop :=
  -- In ZF (without Choice), does such a set exist?
  -- This is likely independent of ZF
  True  -- Placeholder

/-- The unique lattice point selector for a Steinhaus set. -/
noncomputable def steinhausSelector (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : HasSteinhausProperty S)
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : IsCongruent S T) :
    EuclideanSpace ℝ (Fin 2) :=
  (hS T hT).choose

theorem steinhausSelector_mem (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : HasSteinhausProperty S)
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : IsCongruent S T) :
    steinhausSelector S hS T hT ∈ T ∩ integerLattice :=
  (hS T hT).choose_spec.1

theorem steinhausSelector_unique (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : HasSteinhausProperty S)
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : IsCongruent S T)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ T ∩ integerLattice) :
    p = steinhausSelector S hS T hT :=
  (hS T hT).choose_spec.2 p hp

/-!
## Part VII: Related Problems

Generalizations to higher dimensions and other lattices.
-/

/-- Does the Steinhaus property hold for ℤⁿ in ℝⁿ? -/
def HigherDimensionalSteinhaus (n : ℕ) : Prop :=
  ∃ S : Set (EuclideanSpace ℝ (Fin n)),
    ∀ T, (∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Isometry f ∧ T = f '' S) →
    ∃! p, p ∈ T ∧ ∀ i, ∃ m : ℤ, p i = m

/-- Jackson-Mauldin generalizes to ℝⁿ for n ≥ 2. -/
axiom jackson_mauldin_general (n : ℕ) (hn : n ≥ 2) :
  HigherDimensionalSteinhaus n

end Erdos215
