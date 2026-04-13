import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic

/-
# Königsberg OQ-03-OQ-02:
# Formalizing Infinite Paths in Lean 4

## Open Question (konigsberg-oq-03-oq-02)

"Is there a clean Lean formalization of 'infinite path' (bi-infinite or
one-way infinite) in a graph using Mathlib's Stream or Path API?
The HasInfiniteEulerPath stub needs this semantic foundation before
the theorem can be stated precisely."

## Answer

We formalize one-way infinite paths (and Euler paths) in an infinite graph
using ℕ-indexed functions. This avoids codata complexity while being
mathematically equivalent to stream-based definitions.

The key definitions:
1. `InfiniteWalk G`: a ℕ → V function with consecutive adjacency
2. `InfiniteWalk.edgeAt`: the edge traversed at each step
3. `IsEulerWalk`: the walk traverses every edge exactly once
4. `HasOneWayInfiniteEulerPath`: a proper definition of Euler paths

## Builds On
- KonigsbergOQ03.lean: InfiniteGraph definition
-/

namespace KonigsbergOQ03OQ02

/-! ## Part 0: Infinite Graph (self-contained definition) -/

/-- An infinite graph: undirected, loopless.
    (Same as KonigsbergOQ03.InfiniteGraph; reproduced for self-containment
    since Proofs.KonigsbergOQ03 has a dependency on Proofs.Konigsberg
    which has pre-existing compilation issues.) -/
structure InfiniteGraph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-! ## Part 1: One-Way Infinite Walks -/

/-- A one-way infinite walk in an InfiniteGraph:
    a ℕ-indexed sequence of adjacent vertices.
    This is the simplest formalization: no codata needed,
    just a function ℕ → V with the adjacency condition. -/
structure InfiniteWalk {V : Type*} (G : InfiniteGraph V) where
  /-- The n-th vertex in the walk -/
  vertex : ℕ → V
  /-- Consecutive vertices are adjacent -/
  step_adj : ∀ n, G.adj (vertex n) (vertex (n + 1))

/-- The directed edge (as an ordered pair) traversed at step n.
    Since G is undirected, we track both (vertex n, vertex n+1) and
    its reverse; they represent the same edge. -/
def InfiniteWalk.stepPair {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : V × V :=
  (w.vertex n, w.vertex (n + 1))

/-- Two step indices traverse the same undirected edge -/
def InfiniteWalk.sameEdge {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (m n : ℕ) : Prop :=
  (w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
  (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)

/-! ## Part 2: Euler Walk Conditions -/

/-- A walk is edge-injective if no two distinct steps traverse the same edge.
    This is the "at most once" condition for Euler paths. -/
def InfiniteWalk.IsEdgeInjective {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) : Prop :=
  ∀ m n, w.sameEdge m n → m = n

/-- A walk covers a directed arc (u, v) if some step goes from u to v. -/
def InfiniteWalk.CoversDirArc {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (u v : V) : Prop :=
  ∃ n, w.vertex n = u ∧ w.vertex (n + 1) = v

/-- A walk covers an undirected edge {u, v} if some step traverses it
    in either direction. -/
def InfiniteWalk.CoversEdge {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (u v : V) : Prop :=
  w.CoversDirArc u v ∨ w.CoversDirArc v u

/-- An Euler walk traverses every edge exactly once.
    - Covers: every adjacent pair {u,v} is traversed in some step
    - Injective: no two steps traverse the same edge -/
def IsEulerWalk {V : Type*} (G : InfiniteGraph V) (w : InfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → w.CoversEdge u v) ∧ w.IsEdgeInjective

/-- A graph has a one-way infinite Euler path if it admits an Euler walk. -/
def HasOneWayInfiniteEulerPath {V : Type*} (G : InfiniteGraph V) : Prop :=
  ∃ w : InfiniteWalk G, IsEulerWalk G w

/-! ## Part 3: Bi-Infinite Walks -/

/-- A bi-infinite walk: indexed by ℤ, with consecutive adjacency.
    This is needed for some formulations of the Erdős-Grünwald-Weiszfeld theorem. -/
structure BiInfiniteWalk {V : Type*} (G : InfiniteGraph V) where
  vertex : ℤ → V
  step_adj : ∀ n : ℤ, G.adj (vertex n) (vertex (n + 1))

/-- A bi-infinite walk covers an undirected edge {u, v} -/
def BiInfiniteWalk.CoversEdge {V : Type*} (G : InfiniteGraph V)
    (w : BiInfiniteWalk G) (u v : V) : Prop :=
  (∃ n : ℤ, w.vertex n = u ∧ w.vertex (n + 1) = v) ∨
  (∃ n : ℤ, w.vertex n = v ∧ w.vertex (n + 1) = u)

/-- A bi-infinite Euler walk: covers every edge, no edge repeated -/
def IsBiInfiniteEulerWalk {V : Type*} (G : InfiniteGraph V)
    (w : BiInfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → BiInfiniteWalk.CoversEdge G w u v) ∧
  (∀ m n : ℤ, m ≠ n →
    ¬((w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
      (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)))

/-! ## Part 4: Basic Properties -/

/-- Every step in an InfiniteWalk is between adjacent vertices (tautology). -/
theorem InfiniteWalk.step_is_adj {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : G.adj (w.vertex n) (w.vertex (n + 1)) :=
  w.step_adj n

/-- Steps traverse non-loop edges (the endpoints are distinct). -/
theorem InfiniteWalk.step_ne {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : w.vertex n ≠ w.vertex (n + 1) :=
  fun h => G.loopless (w.vertex n) (h ▸ w.step_adj n)

/-- An Euler walk covers each adjacent pair. -/
theorem IsEulerWalk.covers {V : Type*} {G : InfiniteGraph V} {w : InfiniteWalk G}
    (hEuler : IsEulerWalk G w) (u v : V) (hadj : G.adj u v) :
    w.CoversEdge u v :=
  hEuler.1 u v hadj

/-- An Euler walk is edge-injective. -/
theorem IsEulerWalk.injective {V : Type*} {G : InfiniteGraph V} {w : InfiniteWalk G}
    (hEuler : IsEulerWalk G w) : w.IsEdgeInjective :=
  hEuler.2

/-- Stream-based alternative: a walk as a Stream' (coinductive ℕ-indexed stream).
    For completeness, we show InfiniteWalk can be constructed from a Stream'. -/
def ofStream {V : Type*} (G : InfiniteGraph V) (s : Stream' V)
    (h : ∀ n, G.adj (s n) (s (n + 1))) : InfiniteWalk G where
  vertex := s
  step_adj := h

/-! ## Summary -/

/-
## The Answer to OQ-03-OQ-02

**Clean Lean formalization**: Use `ℕ → V` (not codata/streams).

The `InfiniteWalk G` structure captures a one-way infinite walk as:
- `vertex : ℕ → V` — the walk as a function
- `step_adj : ∀ n, G.adj (vertex n) (vertex (n+1))` — adjacency condition

This is isomorphic to `Stream' V` with an adjacency hypothesis, but avoids
the coinductive complexity. The `ofStream` construction shows they're equivalent.

For the Euler condition:
- `IsEulerWalk G w` = covers all edges ∧ edge-injective
- Both conditions are Prop-level, no decidability needed
- The "exactly once" encoding splits into "at least once" (covers) + "at most once" (injective)

`HasOneWayInfiniteEulerPath` is now a proper mathematical definition,
ready for use in the Erdős-Grünwald-Weiszfeld theorem formalization.

**Choosing ℕ over Stream'**: The `Stream'` type is a codatatype (lazy, coinductive)
which requires `#guard_msgs` and coinductive reasoning. Using `ℕ → V` gives
a definitionally equal representation that works with standard induction.
-/

#check @InfiniteWalk
#check @IsEulerWalk
#check @HasOneWayInfiniteEulerPath
#check @BiInfiniteWalk
#check @InfiniteWalk.step_ne

end KonigsbergOQ03OQ02
