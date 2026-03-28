/-
  GraphCore -- Shared Graph Theory Primitives

  Canonical definitions for common graph theory concepts used across
  Erdos problem formalizations. Import this module instead of redefining
  these locally.

  Mirrors the pattern of SzemerediCore.lean for the Szemeredi pipeline.

  Definitions:
  - chromaticNumber: minimum colors for proper coloring (nat)
  - IsKColorable: existence of proper k-coloring
  - minDegree: minimum vertex degree
  - maxDegree: maximum vertex degree
  - inducedSubgraph: subgraph induced by a vertex subset
  - numEdges: number of edges in a finite graph
  - cliqueNumber: size of largest complete subgraph
  - girth: length of shortest cycle (0 if acyclic)
  - diameter: longest shortest path distance (0 if disconnected)

  See also: SzemerediCore.lean for Szemeredi regularity definitions.
-/
import Mathlib

namespace GraphCore

open SimpleGraph Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: Graph Coloring
-/

/-- A graph G is k-colorable if there exists a proper coloring using
    at most k colors, modeled as Fin k. -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ v w : V, G.Adj v w → f v ≠ f w

/-- The chromatic number chi(G): the minimum number of colors needed to
    properly color the vertices of G so that no two adjacent vertices
    share a color. Returns 0 if no finite coloring exists. -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | IsKColorable G k }

/-- A graph contains a k-clique: a set of k pairwise-adjacent vertices. -/
def ContainsClique (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ ∀ v w : V, v ∈ S → w ∈ S → v ≠ w → G.Adj v w

/-
## Part II: Vertex Degrees
-/

/-- Minimum degree of a finite nonempty graph: the smallest number of
    neighbors of any vertex. -/
noncomputable def minDegree [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun v => (G.neighborFinset v).card)

/-- Maximum degree of a finite graph: the largest number of neighbors
    of any vertex. -/
noncomputable def maxDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun v => (G.neighborFinset v).card)

/-
## Part III: Subgraphs and Structure
-/

/-- The induced subgraph on a subset S of V. Vertices are the subtype
    of elements in S, and edges are inherited from G. -/
def inducedSubgraph (G : SimpleGraph V) (S : Set V) : SimpleGraph S where
  Adj v w := G.Adj v.val w.val
  symm _ _ h := G.symm h
  loopless _ h := G.loopless _ h

/-
## Part IV: Edge Counting
-/

/-- Number of edges in a finite graph: the cardinality of the edge set. -/
noncomputable def numEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- Alias for numEdges, used in some formalizations. -/
noncomputable abbrev edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  numEdges G

/-
## Part V: Clique Number
-/

/-- The clique number omega(G): size of the largest complete subgraph.
    This is the maximum k such that G contains K_k. -/
noncomputable def cliqueNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ContainsClique G k }

/-
## Part VI: Girth and Diameter
-/

/-- The girth of a graph: the length of the shortest cycle.
    Returns 0 if the graph is acyclic (a forest).
    Defined as sInf of cycle lengths via Walk.IsCycle. -/
noncomputable def girth (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/-- The diameter of a graph: the maximum over all pairs of vertices of
    the shortest-path distance. Returns 0 for disconnected graphs.
    Uses SimpleGraph.dist (shortest walk length, 0 if unreachable). -/
noncomputable def diameter (G : SimpleGraph V) : ℕ :=
  Finset.sup (Finset.univ ×ˢ Finset.univ) (fun vw => G.dist vw.1 vw.2)

/-
## Part VII: Basic Lemmas
-/

section Lemmas

variable {W : Type*} {G : SimpleGraph W} {k : ℕ}

/-- Colorability is monotone: if G is k-colorable then it is (k+1)-colorable. -/
theorem isKColorable_succ
    (h : IsKColorable G k) : IsKColorable G (k + 1) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun v => ⟨(c v).val, by omega⟩, fun v w hadj => by
    have := hc v w hadj
    simp [Fin.ext_iff] at this ⊢
    exact this⟩

/-- Every graph on a finite type is colorable with |V| colors. -/
theorem exists_colorable [Fintype W] (G' : SimpleGraph W) : ∃ k, IsKColorable G' k := by
  use Fintype.card W
  by_cases h : IsEmpty W
  · exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  · rw [not_isEmpty_iff] at h
    let e := Fintype.equivFin W
    exact ⟨fun v => e v, fun v w hadj heq => by
      have := G'.ne_of_adj hadj
      exact this (e.injective (Fin.ext (Fin.mk.inj heq)))⟩

/-- If G is k-colorable, the induced subgraph on any subset is also k-colorable. -/
theorem inducedSubgraph_isKColorable {S : Set W}
    (hk : IsKColorable G k) : IsKColorable (inducedSubgraph G S) k := by
  obtain ⟨c, hc⟩ := hk
  exact ⟨fun v => c v.val, fun v w hadj => hc v.val w.val hadj⟩

end Lemmas

end GraphCore
