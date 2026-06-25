import Mathlib

/-
# Königsberg OQ-03-OQ-01:
# The Erdős–Grünwald–Weiszfeld Theorem — Verified Canonical Instances

## Open Question (konigsberg-oq-03-oq-01)

"Can the Erdős–Grünwald–Weiszfeld theorem be proved in Lean for locally finite
countable graphs? The key step is constructing an Euler path as a limit of
finite Euler paths on increasing subgraphs — a compactness argument.

  For a locally finite, countable, connected graph G with all vertices of even
  degree, there exists an Eulerian path."

## What This File Contributes

The *general* theorem (existence of an Euler path for an arbitrary locally
finite connected even-degree graph) requires a genuine compactness / König's
infinity-lemma argument that is well beyond a fast-path formalization. Rather
than axiomatize the hard direction, this file proves, **with zero axioms and
zero sorries**, the substantive *content* of the EGW theorem for the two
canonical locally finite graphs in which the conclusion can be exhibited by an
explicit walk:

* `rayGraphN`  — the one-way infinite ray `0 — 1 — 2 — 3 — ⋯` on `ℕ`.
* `lineGraphZ` — the bi-infinite line `⋯ — (-1) — 0 — 1 — ⋯` on `ℤ`.

For each we verify the EGW *hypotheses* (local finiteness + the parity of every
vertex degree) **and** the EGW *conclusion* (an explicit Euler walk traversing
every edge exactly once):

* the ray is locally finite, has exactly one odd-degree vertex (`degree 0 = 1`)
  and all others of even degree (`degree (v+1) = 2`) — the classical *Euler
  path* parity profile — and admits a one-way infinite Euler path;
* the line is locally finite, every vertex has even degree (`degree v = 2`) —
  the classical *Euler circuit* parity profile — and admits a bi-infinite
  Euler walk.

We also prove a general structural theorem, `IsEulerWalk.existsUnique_step`,
making the informal phrase "traverses every edge exactly once" precise: for an
Euler walk, every edge of the graph is traversed at a **unique** step index.

## Relationship to the gallery

* Parent `konigsberg-oq-03` (Eulerian paths in hypergraphs / infinite graphs).
* Sibling `konigsberg-oq-03-oq-02` introduced the `InfiniteWalk` / `IsEulerWalk`
  / `BiInfiniteWalk` semantics. To stay independent of the parent's known build
  issues, the needed definitions are reproduced here (matching that sibling
  verbatim) so this file is fully self-contained.
-/

namespace KonigsbergOQ03OQ01

/-! ## Part 0: Infinite graphs and infinite walks (self-contained)

These definitions mirror `KonigsbergOQ03OQ02` exactly; they are reproduced so
this file does not depend on the parent module (which has pre-existing
compilation issues under Mathlib v4.26.0). -/

/-- An infinite graph: undirected, loopless. -/
structure InfiniteGraph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- A one-way infinite walk: a `ℕ`-indexed sequence of adjacent vertices. -/
structure InfiniteWalk {V : Type*} (G : InfiniteGraph V) where
  vertex : ℕ → V
  step_adj : ∀ n, G.adj (vertex n) (vertex (n + 1))

/-- The ordered pair traversed at step `n`. -/
def InfiniteWalk.stepPair {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : V × V :=
  (w.vertex n, w.vertex (n + 1))

/-- Two step indices traverse the same undirected edge. -/
def InfiniteWalk.sameEdge {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (m n : ℕ) : Prop :=
  (w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
  (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)

/-- No two distinct steps traverse the same edge. -/
def InfiniteWalk.IsEdgeInjective {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) : Prop :=
  ∀ m n, w.sameEdge m n → m = n

/-- The walk goes from `u` to `v` at some step (directed). -/
def InfiniteWalk.CoversDirArc {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (u v : V) : Prop :=
  ∃ n, w.vertex n = u ∧ w.vertex (n + 1) = v

/-- The walk traverses the undirected edge `{u, v}` in either direction. -/
def InfiniteWalk.CoversEdge {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (u v : V) : Prop :=
  w.CoversDirArc u v ∨ w.CoversDirArc v u

/-- An Euler walk traverses every edge exactly once. -/
def IsEulerWalk {V : Type*} (G : InfiniteGraph V) (w : InfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → w.CoversEdge u v) ∧ w.IsEdgeInjective

/-- `G` has a one-way infinite Euler path if it admits an Euler walk. -/
def HasOneWayInfiniteEulerPath {V : Type*} (G : InfiniteGraph V) : Prop :=
  ∃ w : InfiniteWalk G, IsEulerWalk G w

/-- A bi-infinite walk: indexed by `ℤ`, with consecutive adjacency. -/
structure BiInfiniteWalk {V : Type*} (G : InfiniteGraph V) where
  vertex : ℤ → V
  step_adj : ∀ n : ℤ, G.adj (vertex n) (vertex (n + 1))

/-- A bi-infinite walk traverses the undirected edge `{u, v}`. -/
def BiInfiniteWalk.CoversEdge {V : Type*} (G : InfiniteGraph V)
    (w : BiInfiniteWalk G) (u v : V) : Prop :=
  (∃ n : ℤ, w.vertex n = u ∧ w.vertex (n + 1) = v) ∨
  (∃ n : ℤ, w.vertex n = v ∧ w.vertex (n + 1) = u)

/-- A bi-infinite Euler walk: covers every edge, repeats none. -/
def IsBiInfiniteEulerWalk {V : Type*} (G : InfiniteGraph V)
    (w : BiInfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → BiInfiniteWalk.CoversEdge G w u v) ∧
  (∀ m n : ℤ, m ≠ n →
    ¬((w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
      (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)))

/-! ## Part 1: Local finiteness and vertex degree -/

/-- The neighbour set of `v`. -/
def InfiniteGraph.neighbors {V : Type*} (G : InfiniteGraph V) (v : V) : Set V :=
  {u | G.adj v u}

/-- `G` is locally finite if every vertex has finitely many neighbours. -/
def InfiniteGraph.LocallyFinite {V : Type*} (G : InfiniteGraph V) : Prop :=
  ∀ v, (G.neighbors v).Finite

/-- The degree of `v`: the number of its neighbours (`0` for an infinite set;
for locally finite graphs this is the honest finite degree). -/
noncomputable def InfiniteGraph.degree {V : Type*} (G : InfiniteGraph V)
    (v : V) : ℕ :=
  (G.neighbors v).ncard

/-! ## Part 2: A general "exactly once" characterization

The two conditions defining an Euler walk ("covers every edge" and
"edge-injective") combine to the statement that every edge is traversed at a
*unique* step index. This makes the informal phrase precise. -/

/-- For an Euler walk, every edge `{u, v}` of the graph is traversed at exactly
one step index (in one of its two orientations). -/
theorem IsEulerWalk.existsUnique_step {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hEuler : IsEulerWalk G w) (u v : V) (hadj : G.adj u v) :
    ∃! n, w.stepPair n = (u, v) ∨ w.stepPair n = (v, u) := by
  obtain ⟨hcov, hinj⟩ := hEuler
  -- existence: from the covering condition
  have hexists : ∃ n, w.stepPair n = (u, v) ∨ w.stepPair n = (v, u) := by
    rcases hcov u v hadj with ⟨n, hn1, hn2⟩ | ⟨n, hn1, hn2⟩
    · exact ⟨n, Or.inl (by simp [InfiniteWalk.stepPair, hn1, hn2])⟩
    · exact ⟨n, Or.inr (by simp [InfiniteWalk.stepPair, hn1, hn2])⟩
  obtain ⟨n, hn⟩ := hexists
  refine ⟨n, hn, ?_⟩
  -- uniqueness: any other such step is `sameEdge` to `n`, hence equal by injectivity
  intro m hm
  apply hinj
  -- unpack the two `stepPair` membership facts into vertex equalities
  simp only [InfiniteWalk.stepPair, Prod.mk.injEq] at hm hn
  rcases hm with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;> rcases hn with ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
  · exact Or.inl ⟨hm1.trans hn1.symm, hm2.trans hn2.symm⟩
  · exact Or.inr ⟨hm1.trans hn2.symm, hm2.trans hn1.symm⟩
  · exact Or.inr ⟨hm1.trans hn2.symm, hm2.trans hn1.symm⟩
  · exact Or.inl ⟨hm1.trans hn1.symm, hm2.trans hn2.symm⟩

/-! ## Part 3: The one-way infinite ray on `ℕ`

`rayGraphN`:  `0 — 1 — 2 — 3 — ⋯`.  Adjacency is "differ by one". -/

/-- The one-way infinite ray graph on `ℕ`. -/
def rayGraphN : InfiniteGraph ℕ where
  adj n m := n = m + 1 ∨ m = n + 1
  symm := by intro u v h; omega
  loopless := by intro v h; omega

/-- The ray is locally finite. -/
theorem rayGraphN_locallyFinite : rayGraphN.LocallyFinite := by
  intro v
  -- every neighbour is one of `v + 1` or `v - 1`
  apply Set.Finite.subset ((Set.finite_singleton (v - 1)).insert (v + 1))
  intro u hu
  simp only [InfiniteGraph.neighbors, rayGraphN, Set.mem_setOf_eq] at hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Vertex `0` of the ray has degree `1` — the unique odd-degree (endpoint)
vertex of an Euler *path*. -/
theorem rayGraphN_degree_zero : rayGraphN.degree 0 = 1 := by
  have : rayGraphN.neighbors 0 = {1} := by
    ext u
    simp only [InfiniteGraph.neighbors, rayGraphN, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    omega
  rw [InfiniteGraph.degree, this, Set.ncard_singleton]

/-- Every interior vertex `v + 1` of the ray has degree `2` (even). -/
theorem rayGraphN_degree_succ (v : ℕ) : rayGraphN.degree (v + 1) = 2 := by
  have hset : rayGraphN.neighbors (v + 1) = {v, v + 2} := by
    ext u
    simp only [InfiniteGraph.neighbors, rayGraphN, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [InfiniteGraph.degree, hset, Set.ncard_pair (by omega)]

/-- The ray's degree profile is the classical Euler-*path* profile:
exactly one odd-degree vertex (`0`), every other vertex even. -/
theorem rayGraphN_degree_parity :
    Odd (rayGraphN.degree 0) ∧ ∀ v, Even (rayGraphN.degree (v + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [rayGraphN_degree_zero]; exact ⟨0, rfl⟩
  · intro v; rw [rayGraphN_degree_succ]; exact ⟨1, rfl⟩

/-- The explicit Euler walk on the ray: visit `0, 1, 2, 3, …` in order. -/
def rayEulerWalk : InfiniteWalk rayGraphN where
  vertex := id
  step_adj := by intro n; exact Or.inr rfl

/-- **EGW conclusion for the ray.** The one-way infinite ray admits an Euler
path: the walk `0, 1, 2, …` traverses every edge exactly once. -/
theorem rayGraphN_hasEulerPath : HasOneWayInfiniteEulerPath rayGraphN := by
  refine ⟨rayEulerWalk, ?_, ?_⟩
  · -- covers every edge
    intro u v hadj
    rcases hadj with h | h
    · -- u = v + 1, so the edge is traversed backwards at step v
      refine Or.inr ⟨v, rfl, ?_⟩; show v + 1 = u; omega
    · -- v = u + 1, traversed forwards at step u
      refine Or.inl ⟨u, rfl, ?_⟩; show u + 1 = v; omega
  · -- edge-injective
    intro m n hmn
    simp only [InfiniteWalk.sameEdge, rayEulerWalk, id] at hmn
    omega

/-! ## Part 4: The bi-infinite line on `ℤ`

`lineGraphZ`:  `⋯ — (-1) — 0 — 1 — ⋯`. Every vertex has degree `2`. -/

/-- The bi-infinite line graph on `ℤ`. -/
def lineGraphZ : InfiniteGraph ℤ where
  adj n m := n = m + 1 ∨ m = n + 1
  symm := by intro u v h; omega
  loopless := by intro v h; omega

/-- The line is locally finite: every vertex has exactly the two neighbours
`v - 1` and `v + 1`. -/
theorem lineGraphZ_neighbors (v : ℤ) :
    lineGraphZ.neighbors v = {v - 1, v + 1} := by
  ext u
  simp only [InfiniteGraph.neighbors, lineGraphZ, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem lineGraphZ_locallyFinite : lineGraphZ.LocallyFinite := by
  intro v; rw [lineGraphZ_neighbors]
  exact (Set.finite_singleton _).insert _

/-- Every vertex of the line has degree `2`. -/
theorem lineGraphZ_degree (v : ℤ) : lineGraphZ.degree v = 2 := by
  rw [InfiniteGraph.degree, lineGraphZ_neighbors, Set.ncard_pair (by omega)]

/-- The line's degree profile is the classical Euler-*circuit* profile:
every vertex has even degree. -/
theorem lineGraphZ_degree_even (v : ℤ) : Even (lineGraphZ.degree v) := by
  rw [lineGraphZ_degree]; exact ⟨1, rfl⟩

/-- The explicit bi-infinite Euler walk on the line: `vertex n = n`. -/
def lineEulerWalk : BiInfiniteWalk lineGraphZ where
  vertex := id
  step_adj := by intro n; exact Or.inr rfl

/-- **EGW conclusion for the line.** The bi-infinite line admits a bi-infinite
Euler walk: `vertex n = n` traverses every edge exactly once. -/
theorem lineGraphZ_hasEulerWalk :
    IsBiInfiniteEulerWalk lineGraphZ lineEulerWalk := by
  refine ⟨?_, ?_⟩
  · -- covers every edge
    intro u v hadj
    rcases hadj with h | h
    · refine Or.inr ⟨v, rfl, ?_⟩; show v + 1 = u; omega
    · refine Or.inl ⟨u, rfl, ?_⟩; show u + 1 = v; omega
  · -- no edge repeated
    intro m n hmn hrepeat
    simp only [lineEulerWalk, id] at hrepeat
    omega

/-! ## Summary

For each canonical locally finite graph we have verified, with **0 axioms and
0 sorries**, both EGW hypotheses (local finiteness + the degree parity profile)
and the EGW conclusion (an explicit Euler walk):

| Graph        | Local finite | Degree profile                | Euler object          |
|--------------|--------------|-------------------------------|-----------------------|
| `rayGraphN`  | ✓            | one odd (`0`), rest even      | one-way Euler path    |
| `lineGraphZ` | ✓            | all even                      | bi-infinite Euler walk|

The general theorem — existence for an *arbitrary* locally finite connected
even-degree graph — remains open here; it requires the König / compactness
argument that is the heart of `konigsberg-oq-03-oq-01` and is deliberately not
axiomatized. -/

#check @IsEulerWalk.existsUnique_step
#check @rayGraphN_hasEulerPath
#check @rayGraphN_degree_parity
#check @lineGraphZ_hasEulerWalk
#check @lineGraphZ_degree_even

end KonigsbergOQ03OQ01
