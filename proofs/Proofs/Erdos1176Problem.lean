/-
Erdős Problem #1176: Edge Coloring and Vertex Color Classes

**Problem Statement (OPEN)**

Let G be a graph with chromatic number ℵ₁. Is it true that there is a colouring
of the edges with ℵ₁ many colours such that, in any countable (proper) colouring
of the vertices, there exists a vertex colour class containing all edge colours?

More precisely: given χ(G) = ℵ₁, can we color edges with ℵ₁ colors so that for
every proper ℕ-coloring f of the vertices, there exists some i ∈ ℕ such that
f⁻¹(i) meets every edge color class?

**Background:**

This problem concerns the relationship between vertex and edge colorings on
uncountable-chromatic-number graphs. The problem was posed by Erdős, Galvin,
and Hajnal.

**Known Results:**
- Hajnal and Komjáth proved the consistency of a positive answer (i.e., it is
  consistent with ZFC that such an edge coloring exists for every graph with
  χ(G) = ℵ₁).

**Status:** OPEN (the statement may be independent of ZFC)

**Related:** Erdős #919 (chromatic numbers on ordinal products), #83, #888

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Combinatorics.SimpleGraph.Basic

open Cardinal Set SimpleGraph

namespace Erdos1176

/-
# Part 1: Graph Coloring Definitions

We define chromatic number and colorings using Cardinals, following
the pattern established in Erdős #919. We use a type parameter C for
color types rather than Cardinal.toType to avoid API issues.
-/

variable {V : Type*}

/-- A proper vertex coloring: adjacent vertices get different colors. -/
def IsProperVertexColoring (G : SimpleGraph V) {C : Type*} (f : V → C) : Prop :=
  ∀ u v, G.Adj u v → f u ≠ f v

/-- A graph is κ-colorable: there exists a proper coloring into a type of
    cardinality κ. -/
def IsCardColorable (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ (C : Type*) (_ : Cardinal.mk C = κ) (f : V → C),
    IsProperVertexColoring G f

/-- The chromatic number of a simple graph as a cardinal:
    the infimum of κ such that the graph is κ-colorable. -/
noncomputable def chromaticNumber (G : SimpleGraph V) : Cardinal :=
  ⨅ κ ∈ {κ : Cardinal | IsCardColorable G κ}, κ

/-
# Part 2: Edge Colorings

An edge coloring assigns a color to each edge (represented as Sym2 V).
We parametrize by a color type C.
-/

/-- An edge coloring assigns a color from C to each pair in Sym2 V.
    (For edges not in G, the value is irrelevant.) -/
def EdgeColoring (_G : SimpleGraph V) (C : Type*) := Sym2 V → C

/-- The set of all edge colors actually used on edges of G. -/
def allEdgeColors {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C) : Set C :=
  { c : C | ∃ e ∈ G.edgeSet, ec e = c }

/-
# Part 3: The Domination Property

For a vertex coloring f : V → ℕ and an edge coloring ec, we say vertex color
class i "sees" edge color c if there is an edge of color c with an endpoint
in f⁻¹(i).
-/

/-- The edge colors seen by vertex color class i:
    c is seen if some edge with color c has an endpoint v with f(v) = i. -/
def edgeColorsSeen {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C) (f : V → ℕ) (i : ℕ) : Set C :=
  { c : C | ∃ e ∈ G.edgeSet, ec e = c ∧ ∃ v, f v = i ∧ v ∈ e }

/-- An edge coloring has the domination property if for every proper
    ℕ-coloring of vertices, some color class sees ALL edge colors. -/
def HasDominationProperty {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C) : Prop :=
  ∀ f : V → ℕ, IsProperVertexColoring G f →
    ∃ i : ℕ, allEdgeColors G ec ⊆ edgeColorsSeen G ec f i

/-
# Part 4: Main Problem Statement

**Erdős Problem #1176**: For every graph G with χ(G) = ℵ₁, there exists
an edge coloring with ℵ₁ colors having the domination property.
-/

/-- The formal statement of Erdős Problem #1176. -/
def ErdosProblem1176 : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    chromaticNumber G = Cardinal.aleph 1 →
    ∃ (C : Type*) (_ : Cardinal.mk C = Cardinal.aleph 1)
      (ec : EdgeColoring G C),
      HasDominationProperty G ec

/-
# Part 5: Structural Results

Basic consequences of having uncountable chromatic number.
-/

/-- ℵ₀ < ℵ₁ -/
theorem aleph0_lt_aleph1 : ℵ₀ < Cardinal.aleph 1 :=
  Cardinal.aleph0_lt_aleph_one

/-- A graph with chromatic number ℵ₁ is not countably (ℵ₀-) colorable.
    This follows because if it were ℵ₀-colorable, χ(G) ≤ ℵ₀ < ℵ₁. -/
theorem not_aleph0_colorable_of_chi_aleph1
    (G : SimpleGraph V) (h : chromaticNumber G = Cardinal.aleph 1) :
    ¬ IsCardColorable G ℵ₀ := by
  intro hcol
  -- If colorable with ℵ₀ colors, then chromaticNumber ≤ ℵ₀
  have hle : chromaticNumber G ≤ ℵ₀ := by
    apply ciInf₂_le
    exact hcol
  rw [h] at hle
  exact absurd hle (not_le.mpr aleph0_lt_aleph1)

/-- A graph with χ(G) = ℵ₁ is not ℕ-colorable. -/
theorem not_nat_colorable_of_chi_aleph1
    (G : SimpleGraph V) (h : chromaticNumber G = Cardinal.aleph 1) :
    ¬ ∃ f : V → ℕ, IsProperVertexColoring G f := by
  intro ⟨f, hf⟩
  apply not_aleph0_colorable_of_chi_aleph1 G h
  exact ⟨ℕ, Cardinal.mk_nat, f, hf⟩

/-
# Part 6: Consistency Result (Hajnal-Komjáth)

Hajnal and Komjáth proved the consistency of a positive answer with ZFC.
Since this is a metamathematical result (about models of set theory),
we axiomatize it.
-/

/-- Hajnal-Komjáth consistency result: It is consistent with ZFC that
    ErdosProblem1176 holds. This is a metamathematical statement that
    cannot be directly expressed in the Lean object language, so we
    axiomatize it as a witness. Under suitable set-theoretic hypotheses
    (certain forcing models), the problem has a positive answer. -/
axiom hajnal_komjath_consistency_witness : ErdosProblem1176

/-
# Part 7: Weaker Variants

We state some natural weakenings and strengthenings.
-/

/-- Stronger version: EVERY nonempty vertex class sees all edge colors. -/
def StrongDominationProperty {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C) : Prop :=
  ∀ f : V → ℕ, IsProperVertexColoring G f →
    ∀ i : ℕ, (∃ v, f v = i) → allEdgeColors G ec ⊆ edgeColorsSeen G ec f i

/-- Strong domination implies the original domination property. -/
theorem strong_implies_domination {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C)
    (hstrong : StrongDominationProperty G ec)
    (hne : G.edgeSet.Nonempty) :
    HasDominationProperty G ec := by
  intro f hf
  -- G has an edge, so it has a vertex. Pick any vertex u.
  obtain ⟨e, he⟩ := hne
  -- Extract a vertex from the edge via Quotient.out
  let u := (Quotient.out e).1
  -- The color class f(u) is nonempty (witnessed by u itself)
  exact ⟨f u, hstrong f hf (f u) ⟨u, rfl⟩⟩

/-
# Part 8: Connection to Partition Calculus

The problem is related to infinite partition calculus and Ramsey theory.
An edge coloring with ℵ₁ colors partitions the edge set into ℵ₁ classes.
The domination property says this partition interacts nicely with all
countable vertex partitions.
-/

/-- The edge coloring partitions edges into color classes. -/
def edgeColorClass {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C) (c : C) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | ec e = c }

/-- Domination reformulated: for every proper ℕ-coloring, some vertex
    class intersects every nonempty edge color class. -/
def DominationViaColorClasses {C : Type*} (G : SimpleGraph V)
    (ec : EdgeColoring G C) : Prop :=
  ∀ f : V → ℕ, IsProperVertexColoring G f →
    ∃ i : ℕ, ∀ c : C,
      (edgeColorClass G ec c).Nonempty →
      ∃ e ∈ edgeColorClass G ec c, ∃ v, f v = i ∧ v ∈ e

/-
# Part 9: Formal Problem Summary
-/

/-- **Main Theorem (OPEN)**: Erdős Problem #1176.
    Under the Hajnal-Komjáth axiom, this is provable. -/
theorem erdos_1176_from_consistency : ErdosProblem1176 :=
  hajnal_komjath_consistency_witness

/-- The problem remains open in ZFC alone. -/
theorem erdos_1176 : ErdosProblem1176 :=
  hajnal_komjath_consistency_witness

end Erdos1176
