/-
  Königsberg OQ-03: Eulerian Paths in Hypergraphs and Infinite Graphs

  Generalizations of the Euler path/circuit theorem to:
  1. Hypergraphs: edges connect ≥2 vertices
  2. Infinite graphs: countably many vertices/edges

  For hypergraphs, the degree condition generalizes but is not sufficient.
  For infinite graphs, the Erdős-Grünwald-Weiszfeld theorem (1936)
  characterizes when Eulerian paths exist.

  Parent: Konigsberg.lean (Euler's theorem, verified)
-/

import Mathlib

-- The parent `Proofs.Konigsberg` import was removed at 2026-06-01: it is
-- unused here, and the parent currently fails to build under Mathlib v4.26.0
-- (`Nat.odd_iff_not_even` removed; tracked separately by the `konigsberg` slug).

namespace KonigsbergOQ03

-- ============================================================
-- PART I: Eulerian Paths in Hypergraphs
-- ============================================================

/-- An r-uniform hypergraph: edges are r-element subsets of vertices -/
structure RUniformHypergraph (V : Type*) (r : ℕ) where
  edges : Set (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- The degree of a vertex in a hypergraph: number of edges containing it.

The original 2026-04-04 stub used `Finset.univ.filter (fun e => v ∈ e ∧ e ∈ H.edges)`
which requires a `DecidablePred` instance not synthesizable from `H.edges : Set (Finset V)`.
The 2026-06-01 S3 ACT rewrite adds `classical` to invoke `Classical.propDecidable`. -/
noncomputable def hyperDegree {V : Type*} [Fintype V] {r : ℕ}
    (H : RUniformHypergraph V r) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => v ∈ e ∧ (e : Finset V) ∈ H.edges)).card

/-- For a 2-uniform hypergraph (graph case), the underlying `SimpleGraph V`:
two distinct vertices are adjacent iff `{u, v}` is one of the (2-element)
edges of `H`. -/
def toSimpleGraph {V : Type*} [DecidableEq V] (H : RUniformHypergraph V 2) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ ({u, v} : Finset V) ∈ H.edges
  symm := fun u v ⟨hne, hmem⟩ =>
    ⟨hne.symm, by rwa [Finset.pair_comm] at hmem⟩
  loopless := fun v ⟨hne, _⟩ => hne rfl

/-- An Euler tour of a 2-uniform hypergraph: a closed walk in the underlying
`SimpleGraph V` (`toSimpleGraph H`) that visits every edge exactly once.

For `r = 2` the hypergraph case reduces to the standard graph case via
`toSimpleGraph` plus Mathlib's `SimpleGraph.Walk.IsEulerian`. The higher-arity
case `r ≥ 3` requires substantially more machinery (no simple degree condition
suffices — see Lonc–Naroski 2010) and remains a stub elsewhere in this file. -/
def HasEulerTour {V : Type*} [DecidableEq V] (H : RUniformHypergraph V 2) :
    Prop :=
  ∃ u, ∃ p : (toSimpleGraph H).Walk u u, p.IsEulerian

/-- The 2-uniform hypergraph Euler-tour predicate unfolds definitionally to the
corresponding `SimpleGraph.Walk.IsEulerian` characterization on
`toSimpleGraph H`. -/
theorem hasEulerTour_iff_simpleGraph_eulerian {V : Type*} [DecidableEq V]
    (H : RUniformHypergraph V 2) :
    HasEulerTour H ↔ ∃ u, ∃ p : (toSimpleGraph H).Walk u u, p.IsEulerian :=
  Iff.rfl

/- For r ≥ 3, the existence of Euler tours in r-uniform hypergraphs
    is NP-complete (Lonc-Naroski 2010). No simple degree condition suffices. -/

/-- An infinite graph with countably many vertices and edges -/
structure InfiniteGraph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- The degree of a vertex in an infinite graph (possibly infinite).

The original 2026-04-04 stub used `Set.toFinite {w | G.adj v w} |>.toFinset.card`,
which is type-incorrect: `Set.toFinite` requires a `Finite` instance not implied
by `InfiniteGraph`. The 2026-06-01 S3 ACT rewrite uses `Set.encard`, which is
defined for arbitrary sets and returns `⊤ : ℕ∞` for infinite sets — matching
the intended semantics. -/
noncomputable def infiniteDegree {V : Type*} (G : InfiniteGraph V) (v : V) : ℕ∞ :=
  {w | G.adj v w}.encard

/-- An Euler path in an infinite graph: a (possibly infinite) path
    that traverses every edge exactly once -/
def HasInfiniteEulerPath {V : Type*} (G : InfiniteGraph V) : Prop :=
  True  -- requires careful definition of infinite paths

/- Erdős-Grünwald-Weiszfeld theorem (1936):
    A connected countable graph has an Euler path iff:
    1. It has at most 2 vertices of odd degree
    2. Every finite subgraph has an even number of edges -/

/-- A one-way infinite Euler path starts at a vertex and extends
    infinitely, covering every edge exactly once -/
def HasOneWayEulerPath {V : Type*} (G : InfiniteGraph V) : Prop :=
  True  -- path from v₀ through all edges

/- For locally finite infinite graphs (every vertex has finite degree),
    the Euler path criterion is: at most one vertex has odd degree,
    and the graph is connected -/

/- The Chinese Postman Problem: find the shortest closed walk
    that traverses every edge at least once. For finite graphs,
    this is solvable in polynomial time. For infinite graphs,
    the optimal solution may not exist. -/

end KonigsbergOQ03
