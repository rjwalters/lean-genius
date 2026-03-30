/-
Erdős Problem #914: Hajnal-Szemerédi Theorem (Vertex-Disjoint Cliques)

Source: https://erdosproblems.com/914
Status: SOLVED (Hajnal-Szemerédi 1970)

Statement:
Let r ≥ 2 and m ≥ 1. Every graph with rm vertices and minimum degree at least
m(r-1) contains m vertex-disjoint copies of K_r (the complete graph on r vertices).

Background:
This problem, now known as the Hajnal-Szemerédi Theorem, concerns when a graph
contains a perfect K_r-factor: a collection of vertex-disjoint copies of K_r
that together cover all vertices.

Historical Progress:
- r = 2: Follows from Dirac's theorem (perfect matching exists)
- r = 3: Proved by Corrádi and Hajnal (1963)
- r ≥ 4: Proved by Hajnal and Szemerédi (1970)

Key Insight:
The minimum degree condition m(r-1) = rm - m is tight: it requires each vertex
to have enough neighbors to be in a clique with r-1 others from each of m groups.

References:
- Corrádi, Hajnal. "On the maximal number of independent circuits." (1963)
- Hajnal, Szemerédi. "Proof of a conjecture of P. Erdős." (1970)

Tags: graph-theory, extremal-combinatorics, clique-factors
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Degree
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

namespace Erdos914

/- ## Part I: Graph Basics -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Complete Graph K_r:**
The complete graph on r vertices where every pair is adjacent.
-/
abbrev completeGraphOnFin (r : ℕ) := completeGraph (Fin r)

/--
**Minimum Degree:**
The minimum degree δ(G) is the smallest degree over all vertices.
-/
noncomputable def minDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.min' (Finset.univ.image (G.degree ·)) (by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty)

/- ## Part II: Cliques and Clique Covers -/

/--
**r-Clique:**
A set of r vertices that forms a complete subgraph (all pairs adjacent).
-/
def IsRClique (G : SimpleGraph V) (S : Finset V) (r : ℕ) : Prop :=
  S.card = r ∧ G.IsClique S

/--
**Vertex-Disjoint r-Cliques:**
A collection of cliques such that no two share a vertex.
-/
def AreVertexDisjoint (cliques : Finset (Finset V)) : Prop :=
  ∀ C₁ ∈ cliques, ∀ C₂ ∈ cliques, C₁ ≠ C₂ → Disjoint C₁ C₂

/--
**m Vertex-Disjoint K_r's:**
A collection of m vertex-disjoint r-cliques.
-/
def HasMDisjointRCliques (G : SimpleGraph V) (m r : ℕ) : Prop :=
  ∃ cliques : Finset (Finset V),
    cliques.card = m ∧
    (∀ C ∈ cliques, IsRClique G C r) ∧
    AreVertexDisjoint cliques

/--
**Perfect K_r-Factor:**
A collection of vertex-disjoint r-cliques that cover all vertices.
-/
def HasPerfectKrFactor (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ cliques : Finset (Finset V),
    (∀ C ∈ cliques, IsRClique G C r) ∧
    AreVertexDisjoint cliques ∧
    (cliques.biUnion id) = Finset.univ

/- ## Part III: Special Cases -/

/--
**r = 2 Case:**
A graph on 2m vertices with min degree ≥ m has m vertex-disjoint edges.
This follows from Dirac's theorem or basic matching theory.
-/
/--
**Corrádi-Hajnal Theorem (r = 3, 1963):**
A graph on 3m vertices with min degree ≥ 2m contains m vertex-disjoint triangles.
-/
/- ## Part IV: Hajnal-Szemerédi Theorem -/

/--
**Hajnal-Szemerédi Theorem (1970):**
For r ≥ 2 and m ≥ 1, every graph with rm vertices and minimum degree
at least m(r-1) contains m vertex-disjoint copies of K_r.

This is the main result solving Erdős Problem #914.
-/
axiom hajnal_szemeredi (G : SimpleGraph V) [DecidableRel G.Adj] (r m : ℕ) :
    r ≥ 2 →
    m ≥ 1 →
    Fintype.card V = r * m →
    minDegree G ≥ m * (r - 1) →
    HasMDisjointRCliques G m r

/--
**Perfect Clique Factor Form:**
Equivalently: a graph on rm vertices with δ(G) ≥ (r-1)m has a perfect K_r-factor.
Axiomatized since the covering property (biUnion = univ) requires
additional cardinality reasoning beyond the disjoint cliques result.
-/
/- ## Part V: Tightness -/

/--
**Tightness of Minimum Degree:**
The condition δ(G) ≥ m(r-1) is tight. There exist graphs with rm vertices
and minimum degree m(r-1) - 1 that have no m vertex-disjoint K_r's.
-/
axiom degree_condition_tight (r m : ℕ) :
    r ≥ 2 →
    m ≥ 1 →
    ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      Fintype.card V = r * m ∧
      minDegree G = m * (r - 1) - 1 ∧
      ¬HasMDisjointRCliques G m r

/- ## Part VI: Summary

**Erdős Problem #914: SOLVED (Hajnal-Szemerédi 1970)**

**Question:**
Does every graph on rm vertices with minimum degree ≥ m(r-1) contain
m vertex-disjoint copies of K_r?

**Answer:**
YES! Proved by Hajnal and Szemerédi (1970).

**Special Cases:**
- r = 2: Dirac's theorem / matching theory
- r = 3: Corrádi-Hajnal (1963)
- r ≥ 4: Hajnal-Szemerédi (1970)

**Key Properties:**
- The minimum degree condition is tight
- Modern proofs use equitable colorings (Kierstead-Kostochka 2008)
- Polynomial-time algorithms exist (O(n^5), Kierstead et al. 2010)

**Impact:**
A fundamental result in extremal graph theory, showing that high minimum
degree forces spanning structures (not just subgraphs).
-/

/-- **Erdős Problem #914: Summary**

The Hajnal-Szemerédi theorem holds (every graph on rm vertices with
δ ≥ m(r-1) has m vertex-disjoint K_r's) AND the degree bound is tight. -/
theorem erdos_914_summary :
    (∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
      ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj,
      ∀ r m : ℕ, r ≥ 2 → m ≥ 1 →
      Fintype.card V = r * m →
      minDegree G ≥ m * (r - 1) →
      HasMDisjointRCliques G m r) ∧
    (∀ r m : ℕ, r ≥ 2 → m ≥ 1 →
      ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
        Fintype.card V = r * m ∧
        minDegree G = m * (r - 1) - 1 ∧
        ¬HasMDisjointRCliques G m r) :=
  ⟨fun V _ _ G _ r m hr hm hn hδ => hajnal_szemeredi G r m hr hm hn hδ,
   degree_condition_tight⟩

end Erdos914
