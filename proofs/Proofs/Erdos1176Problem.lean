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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.Filter.Basic

open Cardinal Set SimpleGraph

namespace Erdos1176

/-
# Part 1: Graph Infrastructure

We set up the basic graph-theoretic definitions, building on Mathlib's
SimpleGraph and Cardinal infrastructure.
-/

variable {V : Type*}

/-- The chromatic number of a simple graph as a cardinal.
    This is the infimum of cardinals κ such that a proper κ-coloring exists. -/
noncomputable def chromaticNumber (G : SimpleGraph V) : Cardinal :=
  ⨅ κ : Cardinal, if Nonempty (G.Coloring κ.toType) then κ else ⊤

/-- A graph is κ-colorable if there exists a proper coloring with κ colors. -/
def IsCardColorable (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  Nonempty (G.Coloring κ.toType)

/-
# Part 2: Edge Colorings

An edge coloring assigns a color from a set to each edge.
We use Sym2 V for the edges of a SimpleGraph.
-/

/-- An edge coloring of a graph G with color set C.
    Every edge gets exactly one color; non-edges can have arbitrary values. -/
structure EdgeColoring (G : SimpleGraph V) (C : Type*) where
  color : Sym2 V → C

/-- The set of edge colors that appear on edges incident to vertices in a set S. -/
def edgeColorsInducedBy {C : Type*} {G : SimpleGraph V} [DecidableEq V]
    (ec : EdgeColoring G C) (S : Set V) : Set C :=
  { c : C | ∃ e : Sym2 V, e ∈ G.edgeSet ∧ ec.color e = c ∧
    ∃ v ∈ S, v ∈ e }

/-- The set of all edge colors used by the coloring on actual edges of G. -/
def allEdgeColors {C : Type*} {G : SimpleGraph V}
    (ec : EdgeColoring G C) : Set C :=
  { c : C | ∃ e ∈ G.edgeSet, ec.color e = c }

/-
# Part 3: The Main Property

The key property asks: for a vertex coloring f (with countably many colors),
does there exist a color class f⁻¹(i) that "sees" all edge colors?

A vertex color class "sees" an edge color c if some edge colored c has at
least one endpoint in that class.
-/

/-- The set of edge colors "seen" by a vertex color class.
    Color class i sees edge color c if there is an edge of color c with an
    endpoint in f⁻¹(i). -/
def edgeColorsSeen {C : Type*} {G : SimpleGraph V} [DecidableEq V]
    (ec : EdgeColoring G C) (f : V → ℕ) (i : ℕ) : Set C :=
  { c : C | ∃ e ∈ G.edgeSet, ec.color e = c ∧ ∃ v, f v = i ∧ v ∈ e }

/-- The main property: an edge coloring has the "domination" property if
    for every proper vertex ℕ-coloring, some color class sees all edge colors. -/
def HasDominationProperty (G : SimpleGraph V) [DecidableEq V]
    (ec : EdgeColoring G (Cardinal.aleph 1).toType) : Prop :=
  ∀ f : G.Coloring ℕ,
    ∃ i : ℕ, allEdgeColors ec ⊆ edgeColorsSeen ec f i

/-
# Part 4: The Erdős-Galvin-Hajnal Problem

The main conjecture: for graphs with χ(G) = ℵ₁, there exists an edge
coloring with ℵ₁ colors having the domination property.
-/

/-- **Erdős Problem #1176**: For graphs with chromatic number ℵ₁, there
    exists an edge coloring with ℵ₁ colors such that for any countable
    vertex coloring, some color class sees all edge colors. -/
def ErdosProblem1176 : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V) [DecidableEq V],
    chromaticNumber G = Cardinal.aleph 1 →
    ∃ ec : EdgeColoring G (Cardinal.aleph 1).toType,
      HasDominationProperty G ec

/-
# Part 5: Structural Lemmas

We prove some basic structural results about graphs with uncountable
chromatic number.
-/

/-- A graph with chromatic number ℵ₁ is not countably colorable. -/
theorem not_countably_colorable_of_chi_aleph1
    (G : SimpleGraph V) (h : chromaticNumber G = Cardinal.aleph 1) :
    ¬ IsCardColorable G ℵ₀ := by
  intro ⟨c⟩
  -- If G were ℵ₀-colorable, then chromaticNumber G ≤ ℵ₀ < ℵ₁
  have hle : chromaticNumber G ≤ ℵ₀ := by
    apply ciInf_le_of_le (f := fun κ => if Nonempty (G.Coloring κ.toType) then κ else ⊤)
    · exact ⟨0, fun _ _ => zero_le _⟩
    · simp [Nonempty.intro c]
  rw [h] at hle
  exact absurd hle (not_le.mpr (Cardinal.aleph0_lt_aleph 1))

/-- A graph with uncountable chromatic number has nonempty edge set. -/
theorem edgeSet_nonempty_of_chi_uncountable
    (G : SimpleGraph V) (h : ℵ₀ < chromaticNumber G) :
    G.edgeSet.Nonempty := by
  by_contra hempty
  push_neg at hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- If the edge set is empty, the graph is 1-colorable
  have h1 : IsCardColorable G 1 := by
    constructor
    exact ⟨fun _ => ⟨0, Nat.lt_one_iff.mpr rfl⟩, fun v w hadj => by
      exfalso
      exact (hempty ▸ G.edgeSet_subset_edgeSet : G.edgeSet ⊆ ∅) (G.mem_edgeSet.mpr hadj)⟩
  sorry

/-- If we ℕ-color the vertices of a graph with χ(G) = ℵ₁, the coloring
    cannot be a proper coloring with finitely many colors. In particular,
    any proper ℕ-coloring must use infinitely many colors. -/
theorem proper_nat_coloring_uses_infinitely_many
    (G : SimpleGraph V) (h : chromaticNumber G = Cardinal.aleph 1)
    (f : G.Coloring ℕ) :
    Set.Infinite (Set.range f) := by
  sorry

/-
# Part 6: Consistency Result (Hajnal-Komjáth)

Hajnal and Komjáth proved that the positive answer is consistent with ZFC.
This means there exists a model of ZFC where the statement holds.
-/

/-- The Hajnal-Komjáth consistency result:
    It is consistent with ZFC that ErdosProblem1176 holds.
    We axiomatize this as it is a metamathematical statement. -/
axiom hajnal_komjath_consistency :
  -- In Lean we cannot directly state "Con(ZFC + P)" in the object theory.
  -- We record this as: assuming a suitable set-theoretic axiom, the problem holds.
  -- The axiom captures: there exists a model where this is true.
  True -- Placeholder for the metamathematical consistency result

/-
# Part 7: Special Cases and Reductions

We state some consequences and special cases.
-/

/-- For finite graphs, the problem is vacuously true (no finite graph has
    χ = ℵ₁). -/
theorem finite_case_vacuous [Fintype V] (G : SimpleGraph V) :
    chromaticNumber G ≠ Cardinal.aleph 1 := by
  intro h
  have : chromaticNumber G ≤ Cardinal.mk V := by
    apply ciInf_le_of_le (f := fun κ => if Nonempty (G.Coloring κ.toType) then κ else ⊤)
    · exact ⟨0, fun _ _ => zero_le _⟩
    · simp
      sorry
  sorry

/-- A stronger version asks whether the ℵ₁ edge colors can be arranged so that
    EVERY vertex color class sees all edge colors (not just one). -/
def StrongerVersion : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V) [DecidableEq V],
    chromaticNumber G = Cardinal.aleph 1 →
    ∃ ec : EdgeColoring G (Cardinal.aleph 1).toType,
      ∀ f : G.Coloring ℕ, ∀ i : ℕ,
        (∃ v, f v = i) → allEdgeColors ec ⊆ edgeColorsSeen ec f i

/-- The stronger version implies the original. -/
theorem stronger_implies_original :
    StrongerVersion → ErdosProblem1176 := by
  intro hstrong V G _ hchi
  obtain ⟨ec, hec⟩ := hstrong V G hchi
  exact ⟨ec, fun f => by
    -- Any proper coloring uses at least one color
    obtain ⟨v⟩ := G.Coloring.nonempty_of_nonempty (by
      sorry)
    exact ⟨f v, hec f (f v) ⟨v, rfl⟩⟩⟩

/-
# Part 8: Connection to Ramsey Theory

The problem has connections to infinite Ramsey theory and partition calculus.
The edge coloring can be viewed as a partition of the edge set into ℵ₁ pieces.
-/

/-- The number of edge color classes is exactly ℵ₁. -/
def usesAllColors {G : SimpleGraph V}
    (ec : EdgeColoring G (Cardinal.aleph 1).toType) : Prop :=
  ∀ c : (Cardinal.aleph 1).toType, ∃ e ∈ G.edgeSet, ec.color e = c

/-- An edge coloring that uses all ℵ₁ colors and has the domination property
    witnesses a strong partition property. -/
def StrongWitness (G : SimpleGraph V) [DecidableEq V]
    (ec : EdgeColoring G (Cardinal.aleph 1).toType) : Prop :=
  usesAllColors ec ∧ HasDominationProperty G ec

/-
# Part 9: Problem Statement Summary
-/

/-- Formal statement of Erdős Problem #1176.
    OPEN: May be independent of ZFC. -/
theorem erdos_1176 : ErdosProblem1176 := by
  sorry

end Erdos1176
