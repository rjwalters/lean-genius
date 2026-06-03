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

/-! ### Infinite walks and Euler-path predicates

The two `HasInfiniteEulerPath` / `HasOneWayEulerPath` predicates were `:= True`
placeholders prior to the 2026-06-03 S4 ACT. The infrastructure below — a
ℕ-indexed `InfiniteWalk` for the one-way case and a ℤ-indexed `BiInfiniteWalk`
for the bi-infinite case — mirrors the formalisation pattern already shipped
in sibling file `Proofs/KonigsbergOQ03OQ02.lean`, with that file's standalone
`InfiniteGraph` replaced by the parent's own structure to avoid duplication. -/

/-- A one-way infinite walk in an `InfiniteGraph`: a ℕ-indexed sequence of
vertices in which each pair of consecutive vertices is adjacent.

Using `ℕ → V` rather than `Stream' V` avoids coinductive complexity while
remaining mathematically equivalent (the two are interconvertible without
extra hypotheses). -/
structure InfiniteWalk {V : Type*} (G : InfiniteGraph V) where
  /-- The `n`-th vertex of the walk. -/
  vertex : ℕ → V
  /-- Consecutive vertices are adjacent. -/
  step_adj : ∀ n, G.adj (vertex n) (vertex (n + 1))

namespace InfiniteWalk

/-- Two step indices `m`, `n` traverse the same undirected edge: either both
endpoints agree in order, or one is the reverse of the other. -/
def sameEdge {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (m n : ℕ) : Prop :=
  (w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
  (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)

/-- A walk is edge-injective if distinct steps traverse distinct undirected
edges. This is the "at most once" half of the Eulerian condition. -/
def IsEdgeInjective {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) : Prop :=
  ∀ m n, w.sameEdge m n → m = n

/-- The walk covers the directed arc `(u, v)` if some step goes `u → v`. -/
def CoversDirArc {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (u v : V) : Prop :=
  ∃ n, w.vertex n = u ∧ w.vertex (n + 1) = v

/-- The walk covers the undirected edge `{u, v}` if some step traverses it
in either direction. This is the "at least once" half of Eulerian. -/
def CoversEdge {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (u v : V) : Prop :=
  w.CoversDirArc u v ∨ w.CoversDirArc v u

/-- Each step traverses a non-loop edge: the two endpoints are distinct. -/
theorem step_ne {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : w.vertex n ≠ w.vertex (n + 1) :=
  fun h => G.loopless (w.vertex n) (h ▸ w.step_adj n)

end InfiniteWalk

/-- A one-way Euler walk on `G`: a ℕ-indexed walk that covers every edge and
no edge twice. The `G` argument is explicit because Lean cannot infer it from
`w : InfiniteWalk G` in every elaboration context. -/
def IsEulerWalk {V : Type*} (G : InfiniteGraph V) (w : InfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → w.CoversEdge u v) ∧ w.IsEdgeInjective

/-- A bi-infinite walk on `G`: a ℤ-indexed sequence of adjacent vertices.
Needed for the version of the Erdős–Grünwald–Weiszfeld characterisation that
allows the Euler tour to extend to infinity in both directions, rather than
only forward from a chosen starting vertex. -/
structure BiInfiniteWalk {V : Type*} (G : InfiniteGraph V) where
  /-- The vertex at integer index `n`. -/
  vertex : ℤ → V
  /-- Consecutive vertices are adjacent. -/
  step_adj : ∀ n : ℤ, G.adj (vertex n) (vertex (n + 1))

/-- A bi-infinite walk covers the undirected edge `{u, v}` if some integer
index pair traverses it in either direction. -/
def BiInfiniteWalk.CoversEdge {V : Type*} {G : InfiniteGraph V}
    (w : BiInfiniteWalk G) (u v : V) : Prop :=
  (∃ n : ℤ, w.vertex n = u ∧ w.vertex (n + 1) = v) ∨
  (∃ n : ℤ, w.vertex n = v ∧ w.vertex (n + 1) = u)

/-- A bi-infinite Euler walk: covers every edge of `G`, with no edge repeated
across any pair of distinct integer step indices. -/
def IsBiInfiniteEulerWalk {V : Type*} (G : InfiniteGraph V)
    (w : BiInfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → w.CoversEdge u v) ∧
  (∀ m n : ℤ, m ≠ n →
    ¬((w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
      (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)))

/-- An Euler path in an infinite graph: a bi-infinite walk that traverses
every edge of `G` exactly once. This is the bi-infinite version of the
Erdős–Grünwald–Weiszfeld characterisation. -/
def HasInfiniteEulerPath {V : Type*} (G : InfiniteGraph V) : Prop :=
  ∃ w : BiInfiniteWalk G, IsBiInfiniteEulerWalk G w

/- Erdős-Grünwald-Weiszfeld theorem (1936):
    A connected countable graph has an Euler path iff:
    1. It has at most 2 vertices of odd degree
    2. Every finite subgraph has an even number of edges -/

/-- A one-way infinite Euler path starts at a vertex and extends infinitely,
covering every edge exactly once. Formalised as an `InfiniteWalk` together
with the `IsEulerWalk` Eulerian condition. -/
def HasOneWayEulerPath {V : Type*} (G : InfiniteGraph V) : Prop :=
  ∃ w : InfiniteWalk G, IsEulerWalk G w

/- For locally finite infinite graphs (every vertex has finite degree),
    the Euler path criterion is: at most one vertex has odd degree,
    and the graph is connected -/

/- The Chinese Postman Problem: find the shortest closed walk
    that traverses every edge at least once. For finite graphs,
    this is solvable in polynomial time. For infinite graphs,
    the optimal solution may not exist. -/

end KonigsbergOQ03
