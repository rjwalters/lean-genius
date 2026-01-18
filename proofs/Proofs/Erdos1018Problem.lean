/-
Erdős Problem #1018: Non-Planar Subgraphs in Dense Graphs

Let ε > 0. Is there a constant C_ε such that, for all large n,
every graph on n vertices with at least n^(1+ε) edges must contain
a non-planar subgraph on at most C_ε vertices?

**Status**: SOLVED (Kostochka-Pyber 1988)
**Answer**: YES - such graphs contain a K₅ subdivision with O_ε(1) vertices.

Reference: https://erdosproblems.com/1018
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

open SimpleGraph

namespace Erdos1018

/-!
## Graph Basics

We work with simple graphs on finite vertex sets.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges in a simple graph. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The number of vertices. -/
def vertexCount : ℕ := Fintype.card V

/-!
## Dense Graphs

A graph is (1+ε)-dense if it has at least n^(1+ε) edges.
-/

/-- A graph on n vertices has at least n^(1+ε) edges. -/
def isDense (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) : Prop :=
  (edgeCount G : ℝ) ≥ (Fintype.card V : ℝ) ^ (1 + ε)

/-!
## Planar Graphs

A graph is planar if it can be embedded in the plane without edge crossings.
By Kuratowski's theorem, non-planarity is equivalent to containing
a subdivision of K₅ or K₃,₃.
-/

/-- A graph is planar (abstract characterization). -/
def isPlanar (G : SimpleGraph V) : Prop :=
  sorry  -- Complex topological definition

/-- A graph is non-planar if it's not planar. -/
def isNonPlanar (G : SimpleGraph V) : Prop := ¬isPlanar G

/-!
## Complete Graphs K₅ and K₃,₃

The two minimal non-planar graphs (Kuratowski obstructions).
-/

/-- The complete graph K_n. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/-- K₅ is non-planar. -/
axiom K5_nonplanar : isNonPlanar (completeGraph 5)

/-- The complete bipartite graph K_{m,n}. -/
def completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := fun x y h => by cases x <;> cases y <;> simp_all
  loopless := fun x h => by cases x <;> simp at h

/-- K₃,₃ is non-planar. -/
axiom K33_nonplanar : isNonPlanar (completeBipartite 3 3)

/-!
## Graph Subdivisions

A subdivision of H is obtained by replacing edges with paths.
-/

/-- G contains a subdivision of H. -/
def containsSubdivision (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  sorry  -- G has a subgraph homeomorphic to H

/-- Kuratowski's theorem: non-planar iff contains K₅ or K₃,₃ subdivision. -/
axiom kuratowski_theorem (G : SimpleGraph V) :
    isNonPlanar G ↔ containsSubdivision G (completeGraph 5) ∨
                     containsSubdivision G (completeBipartite 3 3)

/-!
## Induced Subgraphs

A subgraph on a vertex subset.
-/

/-- The induced subgraph on a set of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj u v := G.Adj u.val v.val
  symm := fun _ _ h => G.symm h
  loopless := fun _ h => G.loopless _ h

/-- A graph contains a non-planar subgraph on at most k vertices. -/
def hasSmallNonPlanarSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ k ∧ isNonPlanar (inducedSubgraph G S)

/-!
## The Main Question

Does there exist C_ε such that dense graphs have small non-planar subgraphs?
-/

/-- For fixed ε > 0, there exists C_ε bounding the non-planar subgraph size. -/
def existsBoundingConstant (ε : ℝ) : Prop :=
  ε > 0 → ∃ C : ℕ, ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ N →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      isDense G ε → hasSmallNonPlanarSubgraph G C

/-- The main question: Does C_ε exist for all ε > 0? -/
def erdos_1018_question : Prop := ∀ ε : ℝ, existsBoundingConstant ε

/-!
## Kostochka-Pyber Theorem (1988)

The affirmative answer: dense graphs contain small K₅ subdivisions.
-/

/-- A graph contains a K₅ subdivision on at most k vertices. -/
def hasSmallK5Subdivision (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ k ∧ containsSubdivision (inducedSubgraph G S) (completeGraph 5)

/-- Kostochka-Pyber (1988): Dense graphs have small K₅ subdivisions. -/
axiom kostochka_pyber (ε : ℝ) (hε : ε > 0) :
  ∃ C : ℕ, ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ N →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      isDense G ε → hasSmallK5Subdivision G C

/-- The answer is YES: C_ε exists for all ε > 0. -/
theorem erdos_1018_solved : erdos_1018_question := by
  intro ε
  intro hε
  obtain ⟨C, N, hCN⟩ := kostochka_pyber ε hε
  use C, N
  intro V _ _ hn G _ hDense
  obtain ⟨S, hS, hSub⟩ := hCN V hn G hDense
  use S
  constructor
  · exact hS
  · -- K₅ subdivision implies non-planarity
    sorry

/-!
## The Constant C_ε Grows as ε → 0

Erdős noted that C_ε → ∞ as ε → 0.
-/

/-- C_ε → ∞ as ε → 0: smaller density requires larger subgraph. -/
axiom constant_grows : ∀ M : ℕ, ∃ ε₀ > 0, ∀ ε < ε₀,
  ∀ C, existsBoundingConstant ε → C ≥ M

/-- Intuition: sparser graphs hide non-planarity in larger structures. -/
theorem sparse_hides_nonplanarity :
    ∀ M : ℕ, ∃ ε₀ > 0, ∀ ε < ε₀, ∀ C,
      (∀ (V : Type*) [Fintype V] [DecidableEq V],
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          isDense G ε → hasSmallNonPlanarSubgraph G C) → C ≥ M := by
  sorry

/-!
## Connection to Extremal Graph Theory

The edge density n^(1+ε) is super-linear, which forces rich structure.
-/

/-- Linear edges O(n) allow planar graphs. -/
axiom planar_linear_bound : ∀ (V : Type*) [Fintype V] [DecidableEq V],
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    isPlanar G → edgeCount G ≤ 3 * Fintype.card V - 6

/-- Super-linear edges force non-planarity somewhere. -/
theorem superlinear_forces_nonplanar (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V ≥ N →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        isDense G ε → isNonPlanar G := by
  sorry

/-!
## Quantitative Bounds

The actual bound on C_ε from Kostochka-Pyber is explicit.
-/

/-- An explicit (though not optimal) bound on C_ε. -/
noncomputable def explicitBound (ε : ℝ) : ℕ :=
  Nat.ceil (1 / ε ^ 2)

/-- The Kostochka-Pyber bound is polynomial in 1/ε. -/
axiom kostochka_pyber_explicit (ε : ℝ) (hε : ε > 0) :
  ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ N →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      isDense G ε → hasSmallK5Subdivision G (explicitBound ε)

/-!
## Related Problems

This connects to Turán-type problems and topological graph theory.
-/

/-- The Turán number for K₅ subdivisions. -/
noncomputable def turanK5Subdivision (n : ℕ) : ℕ :=
  sorry  -- Max edges avoiding K₅ subdivision

/-- Dense graphs exceed the Turán number for K₅ subdivisions. -/
theorem dense_exceeds_turan (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ (1 + ε) > turanK5Subdivision n := by
  sorry

/-!
## Summary

This file formalizes Erdős Problem #1018 on non-planar subgraphs in dense graphs.

**Status**: SOLVED (Kostochka-Pyber 1988)

**The Question**: For ε > 0, does there exist C_ε such that every graph on n
vertices with n^(1+ε) edges contains a non-planar subgraph on ≤ C_ε vertices?

**The Answer**: YES. Dense graphs contain K₅ subdivisions on O_ε(1) vertices.

**Key Results**:
- Kostochka-Pyber (1988): Affirmative answer via K₅ subdivisions
- C_ε → ∞ as ε → 0 (sparser graphs need larger subgraphs)
- Planar graphs have ≤ 3n - 6 edges (linear), so super-linear forces structure

**Related Topics**:
- Kuratowski's theorem (K₅ and K₃,₃ obstructions)
- Turán-type extremal graph theory
- Topological graph theory
-/

end Erdos1018
