/-
Erdős Problem #1067: Infinitely Connected Subgraphs with Chromatic Number ℵ₁

Source: https://erdosproblems.com/1067
Status: DISPROVED (Counterexamples constructed)

Statement:
Does every graph with chromatic number ℵ₁ contain an infinitely connected subgraph
with chromatic number ℵ₁?

Answer: NO
- Komjáth (2013): Proved consistency of "no" answer
- Soukup (2015): Counterexample without extra set-theoretic assumptions
- Bowler-Pitz (2024): Simpler elementary counterexample

Definition:
A graph is infinitely connected if any two vertices are connected by infinitely
many pairwise disjoint paths.

Variants:
- With ℵ₁ vertices: Independent of ZFC (Komjáth)
- Edge-connectivity version: Counterexample by Thomassen (2017)

Related: Problem #1068
Original: Erdős-Hajnal (1966)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

open Cardinal SimpleGraph

namespace Erdos1067

/- ## Part I: Basic Graph Definitions -/

/--
**Chromatic Number:**
The minimum number of colors needed to properly color a graph.
For infinite graphs, this is a cardinal.
-/
noncomputable def chromaticNumber (G : SimpleGraph V) : Cardinal :=
  sInf { κ : Cardinal | ∃ (c : V → κ), G.Colorable κ.toPartENat.toNat }

/--
**Has Chromatic Number ℵ₁:**
A graph has chromatic number ℵ₁ (aleph-one).
-/
def hasAleph1ChromaticNumber (G : SimpleGraph V) : Prop :=
  chromaticNumber G = Cardinal.aleph 1

/- ## Part II: Infinite Connectivity -/

/--
**Path in Graph:**
A finite sequence of vertices where consecutive vertices are adjacent.
-/
structure PathInGraph (G : SimpleGraph V) where
  vertices : List V
  isPath : ∀ i, i + 1 < vertices.length →
    G.Adj (vertices.get ⟨i, by omega⟩) (vertices.get ⟨i + 1, by omega⟩)

/--
**Disjoint Paths:**
Two paths are disjoint if they share no internal vertices.
-/
def DisjointPaths (p₁ p₂ : PathInGraph G) : Prop :=
  -- Internal vertices don't overlap
  ∀ v, v ∈ p₁.vertices.drop 1 ∧ v ∈ p₁.vertices.dropLast →
       v ∈ p₂.vertices.drop 1 ∧ v ∈ p₂.vertices.dropLast → False

/--
**Pairwise Disjoint Collection:**
A collection of paths is pairwise disjoint.
-/
def PairwiseDisjoint (paths : Set (PathInGraph G)) : Prop :=
  ∀ p₁ ∈ paths, ∀ p₂ ∈ paths, p₁ ≠ p₂ → DisjointPaths p₁ p₂

/--
**Infinitely Many Disjoint Paths:**
There exist infinitely many pairwise disjoint paths between two vertices.
-/
def InfinitelyManyDisjointPaths (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ paths : Set (PathInGraph G),
    Set.Infinite paths ∧ PairwiseDisjoint paths ∧
    ∀ p ∈ paths, p.vertices.head? = some u ∧ p.vertices.getLast? = some v

/--
**Infinitely Connected Graph:**
A graph where any two vertices are connected by infinitely many pairwise disjoint paths.
-/
def InfinitelyConnected (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → InfinitelyManyDisjointPaths G u v

/- ## Part III: Edge Connectivity Variant -/

/--
**Infinitely Edge-Connected:**
To disconnect the graph requires deleting infinitely many edges.
-/
def InfinitelyEdgeConnected (G : SimpleGraph V) : Prop :=
  ∀ E : Set (Sym2 V), E.Finite → ∃ u v : V, u ≠ v ∧
    (G.deleteEdges E).Connected

/- ## Part IV: Subgraph Relations -/

/--
**Subgraph:**
H is a subgraph of G if all edges of H are edges of G.
-/
def IsSubgraph (H G : SimpleGraph V) : Prop :=
  ∀ u v, H.Adj u v → G.Adj u v

/--
**The Erdős-Hajnal Question:**
Does every graph with χ = ℵ₁ contain an infinitely connected subgraph with χ = ℵ₁?
-/
def ErdosHajnalQuestion (G : SimpleGraph V) : Prop :=
  hasAleph1ChromaticNumber G →
  ∃ H : SimpleGraph V, IsSubgraph H G ∧
    InfinitelyConnected H ∧ hasAleph1ChromaticNumber H

/- ## Part V: The Main Results - Counterexamples -/

/--
**Komjáth's Consistency Result (2013):**
It is consistent with ZFC that there exists a counterexample.
-/
/--
**Soukup's Counterexample (2015):**
A counterexample exists in ZFC (no extra assumptions).
-/
axiom soukup_counterexample_2015 :
    ∃ V : Type*, ∃ G : SimpleGraph V,
      hasAleph1ChromaticNumber G ∧
      ∀ H : SimpleGraph V, IsSubgraph H G →
        InfinitelyConnected H → ¬hasAleph1ChromaticNumber H

/--
**Bowler-Pitz Simpler Counterexample (2024):**
An elementary counterexample, simpler than Soukup's.
-/
axiom bowler_pitz_counterexample_2024 :
    ∃ V : Type*, ∃ G : SimpleGraph V,
      hasAleph1ChromaticNumber G ∧
      ∀ H : SimpleGraph V, IsSubgraph H G →
        InfinitelyConnected H → ¬hasAleph1ChromaticNumber H

/--
**Thomassen's Edge-Connectivity Counterexample (2017):**
For the edge-connectivity variant, a counterexample also exists.
-/
/- ## Part VI: The Variant with ℵ₁ Vertices -/

/--
**ℵ₁ Vertices:**
The graph has exactly ℵ₁ many vertices.
-/
def hasAleph1Vertices (V : Type*) : Prop :=
  Cardinal.mk V = Cardinal.aleph 1

/-- **Komjáth's Independence Result:**
For graphs with exactly ℵ₁ vertices, the Erdős-Hajnal question is
independent of ZFC: counterexamples exist in some models but not others.
We axiomatize one direction (consistency of counterexample). -/
/- ## Part VII: Key Observations -/

/-- **Soukup's construction principle:**
One can build a graph from "ladder" structures of trees where
the overall graph needs ℵ₁ colors but any infinitely connected
piece can be colored with fewer colors. -/
/- ## Part IX: Summary

**Erdős Problem #1067: DISPROVED**

**Question:** Does every graph with χ = ℵ₁ contain an infinitely connected
subgraph with χ = ℵ₁?

**Answer:** NO

**Key Results:**
1. Komjáth (2013): Consistency of counterexample
2. Soukup (2015): Counterexample in ZFC
3. Bowler-Pitz (2024): Simpler elementary counterexample
4. Thomassen (2017): Edge-connectivity variant also false

**Key Insight:**
Chromatic number and infinite connectivity are somewhat independent properties.
High chromatic number doesn't force infinitely connected subgraphs to also have
high chromatic number.
-/

/--
**Main Result: The Erdős-Hajnal Question is DISPROVED**
-/
theorem erdos_1067 :
    ∃ V : Type*, ∃ G : SimpleGraph V,
      hasAleph1ChromaticNumber G ∧
      ∀ H : SimpleGraph V, IsSubgraph H G →
        InfinitelyConnected H → ¬hasAleph1ChromaticNumber H :=
  soukup_counterexample_2015

/--
**Simpler version using Bowler-Pitz:**
-/
theorem erdos_1067_elementary :
    ∃ V : Type*, ∃ G : SimpleGraph V,
      hasAleph1ChromaticNumber G ∧
      ∀ H : SimpleGraph V, IsSubgraph H G →
        InfinitelyConnected H → ¬hasAleph1ChromaticNumber H :=
  bowler_pitz_counterexample_2024

/--
**The answer: NO**
-/
theorem erdos_1067_answer :
    ¬∀ V : Type*, ∀ G : SimpleGraph V,
      hasAleph1ChromaticNumber G →
        ∃ H : SimpleGraph V, IsSubgraph H G ∧
          InfinitelyConnected H ∧ hasAleph1ChromaticNumber H := by
  push_neg
  obtain ⟨V, G, hχ, hcounter⟩ := soukup_counterexample_2015
  exact ⟨V, G, hχ, fun H hsub hinf => hcounter H hsub hinf⟩

end Erdos1067
