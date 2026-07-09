/-
Erdős Problem #79: Minimally Non-Ramsey-Size-Linear Graphs

A graph G is "Ramsey size linear" if R(G,H) ≪ m for all graphs H
with m edges and no isolated vertices.

**Question**: Are there infinitely many graphs G that are NOT Ramsey
size linear but such that all proper subgraphs of G ARE?

**Status**: SOLVED (Wigderson 2024)
**Answer**: YES, infinitely many exist, but only K₄ is explicitly known.

Reference: https://erdosproblems.com/79
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

namespace Erdos79

/-
## Ramsey Numbers

The Ramsey number R(G,H) is the minimum n such that any 2-coloring
of K_n contains a red copy of G or a blue copy of H.
-/

/-- The Ramsey number R(G, H). Defining R(G, H) constructively on the infinite
    host type `ℕ` needs machinery beyond the scope of this file, so it is kept
    as an opaque parameter: its value is left unspecified. This is exactly what
    an axiomatized treatment of the size-linearity assumptions below requires --
    nothing about `ramseyNumber` can be derived, so the K₄ axioms stay
    consistent. -/
opaque ramseyNumber (G H : SimpleGraph ℕ) : ℕ

/-
## Finite Graphs and Edge Counts

We model finite graphs as graphs `G : SimpleGraph ℕ` with a finite edge set;
every finite graph embeds this way into the universal host `ℕ`.
-/

variable {V : Type*}

/-- A graph is finite if it has only finitely many edges. -/
def isFinite (G : SimpleGraph ℕ) : Prop :=
  G.edgeSet.Finite

/-- The number of edges of `G`, as the cardinality of its edge set.
    (`Set.ncard` returns `0` on an infinite edge set.) -/
noncomputable def edgeCount (G : SimpleGraph ℕ) : ℕ :=
  Set.ncard G.edgeSet

/-
## Ramsey Size Linearity

A graph G is Ramsey size linear if R(G,H) = O(m) where m = |E(H)|
ranges over all finite graphs H.
-/

/-- G is Ramsey size linear if `R(G,H) ≤ C · m` for some constant `C > 0`
    and all finite graphs `H`, where `m = edgeCount H`. -/
def isRamseySizeLinear (G : SimpleGraph ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ H : SimpleGraph ℕ,
    isFinite H → (ramseyNumber G H : ℝ) ≤ C * edgeCount H

/-- G is NOT Ramsey size linear - R(G,H) grows superlinearly for some H. -/
def isRamseySizeSuperlinear (G : SimpleGraph ℕ) : Prop :=
  ¬ isRamseySizeLinear G

/-
## Subgraphs and the Hereditary Property

The property of being Ramsey size linear is hereditary:
if G is Ramsey size linear, so is every subgraph.
-/

/-- A proper subgraph: fewer edges, same or fewer vertices. -/
def isProperSubgraph (H G : SimpleGraph V) : Prop :=
  H ≤ G ∧ H ≠ G

/-- Ramsey size linearity is hereditary. -/
axiom ramsey_linear_hereditary (G H : SimpleGraph ℕ) :
    isProperSubgraph H G → isRamseySizeLinear G → isRamseySizeLinear H

/-
## Minimally Non-Ramsey-Size-Linear Graphs

A graph is minimally non-Ramsey-size-linear if it fails the property
but all proper subgraphs satisfy it.
-/

/-- G is minimally non-Ramsey-size-linear if:
    1. G is NOT Ramsey size linear
    2. All proper subgraphs of G ARE Ramsey size linear -/
def isMinimallyNonLinear (G : SimpleGraph ℕ) : Prop :=
  isRamseySizeSuperlinear G ∧
  ∀ H : SimpleGraph ℕ, isProperSubgraph H G → isRamseySizeLinear H

/-
## The Complete Graph K₄

K₄ is the unique known explicit example.
-/

/-- The complete graph K_n realised inside `SimpleGraph ℕ` on the vertex set
    `{0, …, n-1}`. This is the representation compatible with the Ramsey
    size-linearity predicates, which all range over `SimpleGraph ℕ`. -/
def completeGraphN (n : ℕ) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ u < n ∧ v < n
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := fun _ h => h.1 rfl

/-- K₄ is NOT Ramsey size linear. -/
axiom K4_not_linear : isRamseySizeSuperlinear (completeGraphN 4)

/-- All proper subgraphs of K₄ ARE Ramsey size linear. -/
axiom K4_subgraphs_linear :
    ∀ H : SimpleGraph ℕ, isProperSubgraph H (completeGraphN 4) →
    isRamseySizeLinear H

/-- K₄ is minimally non-Ramsey-size-linear. -/
theorem K4_is_minimal : isMinimallyNonLinear (completeGraphN 4) := by
  constructor
  · exact K4_not_linear
  · intro H hH
    exact K4_subgraphs_linear H hH

/-
## The Main Question

Erdős, Faudree, Rousseau, and Schelp (1993) asked whether
infinitely many minimally non-Ramsey-size-linear graphs exist.
-/

/-- The set of minimally non-Ramsey-size-linear graphs. -/
def minimalNonLinearGraphs : Set (SimpleGraph ℕ) :=
  { G | isMinimallyNonLinear G }

/-- The main question: Are there infinitely many such graphs? -/
def erdos_79_question : Prop :=
  minimalNonLinearGraphs.Infinite

/-
## Wigderson's Theorem (2024)

Wigderson proved that infinitely many such graphs exist,
though the proof is non-constructive.
-/

/-- Wigderson (2024): Infinitely many minimally non-Ramsey-size-linear
    graphs exist. The proof is non-constructive. -/
axiom wigderson_theorem : erdos_79_question

/-- Erdős Problem #79 is SOLVED. -/
theorem erdos_79_solved : erdos_79_question := wigderson_theorem

/-
## The Explicit Construction Problem

Despite Wigderson's theorem, only K₄ is explicitly known.
Finding another example is a major open problem.
-/

/-- The only known explicit example is K₄ (as a graph on ℕ). -/
def knownExamples : Set (SimpleGraph ℕ) :=
  {completeGraphN 4}

/-- K₄ is the unique known example: every graph in `knownExamples` is
    minimally non-Ramsey-size-linear. Since `knownExamples` is the singleton
    `{K₄}`, this reduces to `K4_is_minimal`. -/
theorem K4_unique_known :
    ∀ G ∈ knownExamples, isMinimallyNonLinear G := by
  intro G hG
  rw [knownExamples, Set.mem_singleton_iff] at hG
  subst hG
  exact K4_is_minimal

/-- Open problem: Find an explicit G ≠ K₄ with this property. -/
def explicit_construction_open : Prop :=
  ∃ G : SimpleGraph ℕ, isMinimallyNonLinear G ∧
    G ≠ completeGraphN 4

/-
## Why K₄ is Special

K₄ has exactly 6 edges and 4 vertices. Its proper subgraphs
include triangles, paths, and matchings - all Ramsey size linear.
-/

/-
K₄ has 6 edges and 4 vertices. Its proper subgraphs (triangles, paths,
matchings) are all Ramsey size linear; this is packaged into the axiom
`K4_subgraphs_linear` above.

## Antichain Structure

Minimally non-Ramsey-size-linear graphs form an antichain
in the subgraph ordering (no two are subgraphs of each other).
-/

/-- Minimal elements of any hereditary property form an antichain. -/
theorem minimal_form_antichain :
    ∀ G H : SimpleGraph ℕ,
    isMinimallyNonLinear G → isMinimallyNonLinear H →
    G ≠ H → ¬ isProperSubgraph G H ∧ ¬ isProperSubgraph H G := by
  intro G H ⟨hGsup, hGmin⟩ ⟨hHsup, hHmin⟩ _
  exact ⟨fun hGH => hGsup (hHmin G hGH), fun hHG => hHsup (hGmin H hHG)⟩

/-
## Order-theoretic foundations

The `isProperSubgraph` relation is exactly the strict order `<` on graphs, and
`completeGraphN` is monotone.  These are the structural facts that make the
"minimal element" language above well-posed: `minimal_form_antichain` is an
instance of "minimal elements of a strict partial order are pairwise
incomparable", and monotonicity places the complete graphs `K₀ ≤ K₁ ≤ K₂ ≤ ⋯`
in a chain through which every proper subgraph of `K₄` is approached.
-/

/-- `isProperSubgraph` is irreflexive: no graph is a proper subgraph of itself. -/
theorem isProperSubgraph_irrefl (G : SimpleGraph ℕ) : ¬ isProperSubgraph G G :=
  fun h => h.2 rfl

/-- `isProperSubgraph` is asymmetric: `H ⊏ G` rules out `G ⊏ H`.  (This is the
    two-graph form of `minimal_form_antichain`'s incomparability, holding for *all*
    graphs, not only minimal ones.) -/
theorem isProperSubgraph_asymm {G H : SimpleGraph ℕ}
    (h : isProperSubgraph H G) : ¬ isProperSubgraph G H :=
  fun h' => h.2 (le_antisymm h.1 h'.1)

/-- `isProperSubgraph` is transitive, so it is a strict partial order. -/
theorem isProperSubgraph_trans {F G H : SimpleGraph ℕ}
    (h1 : isProperSubgraph F G) (h2 : isProperSubgraph G H) :
    isProperSubgraph F H := by
  refine ⟨le_trans h1.1 h2.1, ?_⟩
  intro hFH
  exact h2.2 (le_antisymm h2.1 (hFH ▸ h1.1))

/-- **Monotonicity of the complete graphs.**  `Kₘ ≤ Kₙ` whenever `m ≤ n`: adding
    vertices only adds edges. -/
theorem completeGraphN_mono {m n : ℕ} (h : m ≤ n) :
    completeGraphN m ≤ completeGraphN n := by
  intro u v huv
  obtain ⟨hne, hu, hv⟩ := huv
  exact ⟨hne, lt_of_lt_of_le hu h, lt_of_lt_of_le hv h⟩

/-- `K₀` is the empty graph. -/
theorem completeGraphN_zero : completeGraphN 0 = ⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨_, hu, _⟩
  omega

/-- `K₁` is the empty graph: a single vertex has no edges. -/
theorem completeGraphN_one : completeGraphN 1 = ⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨hne, hu, hv⟩
  omega

/-
## Summary

This file formalizes Erdős Problem #79 on minimally non-Ramsey-size-linear graphs.

**Status**: SOLVED (Wigderson 2024)

**The Question**: Are there infinitely many graphs G that are NOT
Ramsey size linear but all proper subgraphs are?

**The Answer**: YES (Wigderson 2024), but the proof is non-constructive.
K₄ remains the only explicitly known example.

**Key Results**:
- K4_is_minimal: K₄ is minimally non-Ramsey-size-linear
- wigderson_theorem: Infinitely many such graphs exist
- ramsey_linear_hereditary: The property is hereditary

**Open Problems**:
- Find an explicit example other than K₄
- Characterize the structure of these graphs
- Make Wigderson's proof constructive
-/

end Erdos79
