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
  symm.symm := fun u v ⟨hne, hmem⟩ =>
    ⟨hne.symm, by rwa [Finset.pair_comm] at hmem⟩
  loopless.irrefl := fun v ⟨hne, _⟩ => hne rfl

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

/-- Every step in an `InfiniteWalk` is between adjacent vertices (tautology).
Mirrors the sibling `KonigsbergOQ03OQ02.InfiniteWalk.step_is_adj` accessor. -/
theorem step_is_adj {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (n : ℕ) : G.adj (w.vertex n) (w.vertex (n + 1)) :=
  w.step_adj n

end InfiniteWalk

/-- A one-way Euler walk on `G`: a ℕ-indexed walk that covers every edge and
no edge twice. The `G` argument is explicit because Lean cannot infer it from
`w : InfiniteWalk G` in every elaboration context. -/
def IsEulerWalk {V : Type*} (G : InfiniteGraph V) (w : InfiniteWalk G) : Prop :=
  (∀ u v, G.adj u v → w.CoversEdge u v) ∧ w.IsEdgeInjective

namespace IsEulerWalk

/-- An Euler walk covers each adjacent pair (projection of the `And`).
Mirrors the sibling `KonigsbergOQ03OQ02.IsEulerWalk.covers` accessor. -/
theorem covers {V : Type*} {G : InfiniteGraph V} {w : InfiniteWalk G}
    (hEuler : IsEulerWalk G w) (u v : V) (hadj : G.adj u v) :
    w.CoversEdge u v :=
  hEuler.1 u v hadj

/-- An Euler walk is edge-injective (projection of the `And`).
Mirrors the sibling `KonigsbergOQ03OQ02.IsEulerWalk.injective` accessor. -/
theorem injective {V : Type*} {G : InfiniteGraph V} {w : InfiniteWalk G}
    (hEuler : IsEulerWalk G w) : w.IsEdgeInjective :=
  hEuler.2

end IsEulerWalk

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

/-! ### No-edge sanity theorems

The smallest non-trivial Eulerian facts: an `InfiniteGraph` with no edges
admits no infinite walks at all, hence has no (one-way or bi-infinite)
Euler path. These confirm the predicates from the 2026-06-03 S4 ACT are
non-degenerate (they do *not* hold vacuously for every graph). -/

/-- A no-edge `InfiniteGraph` admits no `InfiniteWalk`: any candidate walk's
step-0 adjacency contradicts the no-edge hypothesis. -/
theorem InfiniteWalk.isEmpty_of_no_edges {V : Type*} {G : InfiniteGraph V}
    (h : ∀ u v, ¬ G.adj u v) : IsEmpty (InfiniteWalk G) :=
  ⟨fun w => h _ _ (w.step_adj 0)⟩

/-- A no-edge `InfiniteGraph` admits no `BiInfiniteWalk`. -/
theorem BiInfiniteWalk.isEmpty_of_no_edges {V : Type*} {G : InfiniteGraph V}
    (h : ∀ u v, ¬ G.adj u v) : IsEmpty (BiInfiniteWalk G) :=
  ⟨fun w => h _ _ (w.step_adj 0)⟩

/-- A no-edge `InfiniteGraph` has no one-way Euler path: the existential is
unsatisfiable because the walk type itself is empty. -/
theorem not_hasOneWayEulerPath_of_no_edges {V : Type*} {G : InfiniteGraph V}
    (h : ∀ u v, ¬ G.adj u v) : ¬ HasOneWayEulerPath G := by
  rintro ⟨w, _⟩
  exact h _ _ (w.step_adj 0)

/-- A no-edge `InfiniteGraph` has no bi-infinite Euler path. -/
theorem not_hasInfiniteEulerPath_of_no_edges {V : Type*} {G : InfiniteGraph V}
    (h : ∀ u v, ¬ G.adj u v) : ¬ HasInfiniteEulerPath G := by
  rintro ⟨w, _⟩
  exact h _ _ (w.step_adj 0)

/-! ### Single-edge sanity theorems

The next-smallest Eulerian facts: an `InfiniteGraph` whose *only* edge is the
single undirected edge `{u, v}` (`u ≠ v`) supports no Euler path. Any infinite
walk must traverse an edge at *every* step, so with one edge available the walk
is forced to bounce `u → v → u → ⋯`; steps `0` and `1` then traverse the same
edge `{u, v}`, contradicting the edge-injectivity ("no edge twice") half of the
Eulerian condition. The hypothesis `hone` says every edge of `G` equals `{u, v}`
(equivalently, `G` has at most this one undirected edge). -/

/-- A single-edge `InfiniteGraph` (every edge is `{u, v}`, `u ≠ v`) has no
bi-infinite Euler path: the walk must bounce `u ↔ v`, so steps `0` and `1`
repeat the edge `{u, v}`, violating edge-injectivity. -/
theorem not_hasInfiniteEulerPath_of_single_edge {V : Type*} {G : InfiniteGraph V}
    {u v : V} (huv : u ≠ v)
    (hone : ∀ a b, G.adj a b → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ¬ HasInfiniteEulerPath G := by
  rintro ⟨w, -, hinj⟩
  have s0 := hone _ _ (w.step_adj 0)
  have s1 := hone _ _ (w.step_adj 1)
  simp only [zero_add] at s0
  have hv02 : w.vertex 0 = w.vertex (1 + 1) := by
    rcases s0 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases s1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd (h1.symm.trans ha) huv.symm
    · rw [h0, hb]
    · rw [h0, hb]
    · exact absurd (h1.symm.trans ha) huv
  exact hinj 0 1 (by norm_num) (Or.inr ⟨hv02, by rw [zero_add]⟩)

/-- A single-edge `InfiniteGraph` (every edge is `{u, v}`, `u ≠ v`) has no
one-way Euler path, by the same bounce argument on the ℕ-indexed walk. -/
theorem not_hasOneWayEulerPath_of_single_edge {V : Type*} {G : InfiniteGraph V}
    {u v : V} (huv : u ≠ v)
    (hone : ∀ a b, G.adj a b → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ¬ HasOneWayEulerPath G := by
  rintro ⟨w, -, hinj⟩
  have s0 := hone _ _ (w.step_adj 0)
  have s1 := hone _ _ (w.step_adj 1)
  have hv02 : w.vertex 0 = w.vertex (1 + 1) := by
    rcases s0 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases s1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd (h1.symm.trans ha) huv.symm
    · rw [h0, hb]
    · rw [h0, hb]
    · exact absurd (h1.symm.trans ha) huv
  exact absurd (hinj 0 1 (Or.inr ⟨hv02, rfl⟩)) (by norm_num)

/-! ### Finite-edge generalization

The common core of the no-edge and single-edge impossibility theorems above:
an infinite Euler walk must traverse a *fresh* edge at every step, so it
injects its (infinite) index set into the edge set of `G`. Hence any
`InfiniteGraph` with only finitely many edges — in particular any graph on
finitely many vertices — admits no one-way and no bi-infinite Euler path.

Finiteness is phrased via the set of *directed arcs*
`{p : V × V | G.adj p.1 p.2}`: the arc set is finite iff the undirected edge
set is (each undirected edge contributes exactly two arcs), and the directed
form lets the step map `n ↦ (vertex n, vertex (n + 1))` land in it without
passing through `Sym2`. -/

/-- The set of directed arcs of an `InfiniteGraph`: ordered pairs of adjacent
vertices. Finite iff the undirected edge set is finite. -/
def arcSet {V : Type*} (G : InfiniteGraph V) : Set (V × V) :=
  {p | G.adj p.1 p.2}

/-- No edge-injective infinite walk exists in a graph with finitely many
arcs: the step map `n ↦ (vertex n, vertex (n + 1))` is injective (equal
directed arcs at distinct steps would repeat an undirected edge), so it would
inject `ℕ` into the finite arc set. Note only the edge-*injectivity* half of
the Eulerian condition is needed, so this is stated at walk level. -/
theorem InfiniteWalk.not_isEdgeInjective_of_finite_arcs {V : Type*}
    {G : InfiniteGraph V} (hfin : (arcSet G).Finite) (w : InfiniteWalk G) :
    ¬ w.IsEdgeInjective := by
  intro hinj
  have hstep : Function.Injective fun n => (w.vertex n, w.vertex (n + 1)) := by
    intro m n hmn
    simp only [Prod.mk.injEq] at hmn
    exact hinj m n (Or.inl hmn)
  exact absurd
    (Set.infinite_of_injective_forall_mem hstep fun n => w.step_adj n)
    hfin.not_infinite

/-- A finite-arc `InfiniteGraph` has no one-way Euler path. Strictly
generalizes `not_hasOneWayEulerPath_of_no_edges` and
`not_hasOneWayEulerPath_of_single_edge`. -/
theorem not_hasOneWayEulerPath_of_finite_arcs {V : Type*} {G : InfiniteGraph V}
    (hfin : (arcSet G).Finite) : ¬ HasOneWayEulerPath G := by
  rintro ⟨w, hEuler⟩
  exact InfiniteWalk.not_isEdgeInjective_of_finite_arcs hfin w hEuler.2

/-- A finite-arc `InfiniteGraph` has no bi-infinite Euler path: the ℤ-indexed
step map would inject `ℤ` into the finite arc set. Strictly generalizes
`not_hasInfiniteEulerPath_of_no_edges` and
`not_hasInfiniteEulerPath_of_single_edge`. -/
theorem not_hasInfiniteEulerPath_of_finite_arcs {V : Type*} {G : InfiniteGraph V}
    (hfin : (arcSet G).Finite) : ¬ HasInfiniteEulerPath G := by
  rintro ⟨w, -, hinj⟩
  have hstep : Function.Injective fun n : ℤ => (w.vertex n, w.vertex (n + 1)) := by
    intro m n hmn
    by_contra hne
    simp only [Prod.mk.injEq] at hmn
    exact hinj m n hne (Or.inl hmn)
  exact absurd
    (Set.infinite_of_injective_forall_mem hstep fun n => w.step_adj n)
    hfin.not_infinite

/-- A graph on finitely many vertices has no one-way Euler path: infinite
Euler walks need infinitely many edges, hence infinitely many vertices. -/
theorem not_hasOneWayEulerPath_of_finite {V : Type*} [Finite V]
    (G : InfiniteGraph V) : ¬ HasOneWayEulerPath G :=
  not_hasOneWayEulerPath_of_finite_arcs (Set.toFinite _)

/-- A graph on finitely many vertices has no bi-infinite Euler path. -/
theorem not_hasInfiniteEulerPath_of_finite {V : Type*} [Finite V]
    (G : InfiniteGraph V) : ¬ HasInfiniteEulerPath G :=
  not_hasInfiniteEulerPath_of_finite_arcs (Set.toFinite _)

/-! ### Satisfiability witnesses (S12)

Everything above is an *impossibility* theorem. The predicates are only
meaningful if some graph actually satisfies them, so this section provides the
two canonical positive witnesses:

* the **ray graph** on `ℕ` (`n ~ n + 1`) has a one-way Euler path — the
  identity walk `0 → 1 → 2 → ⋯` traverses each edge `{n, n+1}` exactly once;
* the **line graph** on `ℤ` (`n ~ n + 1`) has a bi-infinite Euler path — the
  identity `ℤ`-walk.

Combining each witness with the S11 finite-arc impossibility theorems yields
the (necessarily true) corollaries that both graphs have infinitely many arcs
— the finiteness obstruction is the *only* thing the S11 theorems rule out,
and these graphs clear it. -/

/-- The ray graph on `ℕ`: `m` and `n` are adjacent iff they are consecutive.
The prototypical one-ended infinite graph. -/
def rayGraph : InfiniteGraph ℕ where
  adj m n := m + 1 = n ∨ n + 1 = m
  symm := fun _ _ h => h.symm
  loopless := fun _ h => by omega

/-- The identity walk `0 → 1 → 2 → ⋯` on the ray graph. -/
def rayWalk : InfiniteWalk rayGraph where
  vertex := id
  step_adj := fun _ => Or.inl rfl

/-- The identity walk is an Euler walk on the ray graph: every edge `{n, n+1}`
is traversed (at step `n`), and distinct steps traverse distinct edges (step
`m` traverses `{m, m+1}`, and `{m, m+1} = {n, n+1}` forces `m = n`). -/
theorem rayWalk_isEulerWalk : IsEulerWalk rayGraph rayWalk := by
  constructor
  · intro u v hadj
    rcases hadj with h | h
    · exact Or.inl ⟨u, rfl, h⟩
    · exact Or.inr ⟨v, rfl, h⟩
  · intro m n hmn
    rcases hmn with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [rayWalk, id] at h1 h2 <;> omega

/-- **The ray graph has a one-way Euler path** — the first satisfiability
witness for `HasOneWayEulerPath`, complementing the S11 impossibility
theorems. -/
theorem rayGraph_hasOneWayEulerPath : HasOneWayEulerPath rayGraph :=
  ⟨rayWalk, rayWalk_isEulerWalk⟩

/-- The ray graph has infinitely many arcs: it has a one-way Euler path, which
`not_hasOneWayEulerPath_of_finite_arcs` forbids for finite-arc graphs. -/
theorem rayGraph_arcSet_infinite : (arcSet rayGraph).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  exact not_hasOneWayEulerPath_of_finite_arcs hfin rayGraph_hasOneWayEulerPath

/-- The line graph on `ℤ`: `m` and `n` are adjacent iff they are consecutive.
The prototypical two-ended infinite graph. -/
def lineGraph : InfiniteGraph ℤ where
  adj m n := m + 1 = n ∨ n + 1 = m
  symm := fun _ _ h => h.symm
  loopless := fun _ h => by omega

/-- The identity `ℤ`-walk `⋯ → -1 → 0 → 1 → ⋯` on the line graph. -/
def lineWalk : BiInfiniteWalk lineGraph where
  vertex := id
  step_adj := fun _ => Or.inl rfl

/-- The identity `ℤ`-walk is a bi-infinite Euler walk on the line graph. -/
theorem lineWalk_isBiInfiniteEulerWalk : IsBiInfiniteEulerWalk lineGraph lineWalk := by
  constructor
  · intro u v hadj
    rcases hadj with h | h
    · exact Or.inl ⟨u, rfl, h⟩
    · exact Or.inr ⟨v, rfl, h⟩
  · intro m n hne hcon
    rcases hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [lineWalk, id] at h1 h2 <;> omega

/-- **The line graph on `ℤ` has a bi-infinite Euler path** — the first
satisfiability witness for `HasInfiniteEulerPath`. -/
theorem lineGraph_hasInfiniteEulerPath : HasInfiniteEulerPath lineGraph :=
  ⟨lineWalk, lineWalk_isBiInfiniteEulerWalk⟩

/-- The line graph has infinitely many arcs, by the same contrapositive
pairing of the S12 witness with the S11 impossibility theorem. -/
theorem lineGraph_arcSet_infinite : (arcSet lineGraph).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  exact not_hasInfiniteEulerPath_of_finite_arcs hfin lineGraph_hasInfiniteEulerPath

/-! ### Incomparability of the two Euler-path notions (S13)

The S12 witnesses show `rayGraph` satisfies `HasOneWayEulerPath` and
`lineGraph` satisfies `HasInfiniteEulerPath`. This section proves the two
*negative* halves of the picture:

* `rayGraph` has **no** bi-infinite Euler path — vertex `0` has degree one,
  but a `ℤ`-indexed walk must both enter and leave every vertex it visits,
  so the steps into and out of `0` would each traverse the unique edge
  `{0, 1}`, violating edge-injectivity;
* `lineGraph` has **no** one-way Euler path — a `ℕ`-indexed Euler walk
  crosses the cut `{…, -1, 0} | {1, 2, …}` exactly once (the crossing edge
  `{0, 1}` may only be traversed once), after which it is trapped on one
  side; the infinitely many edges on the abandoned side would all have to be
  traversed within the finitely many steps before the crossing.

Hence neither Euler-path predicate implies the other: the one-ended ray and
the two-ended line separate them in both directions. This is the formal core
of the classical observation that the *ends* of an infinite graph govern
which kind of Euler path it can carry (Erdős–Grünwald–Weiszfeld 1936). -/

/-- **The ray graph has no bi-infinite Euler path.** Vertex `0` has degree
one: its only incident edge is `{0, 1}`. A bi-infinite walk visiting `0` must
both arrive and depart through that edge, so two distinct steps traverse
`{0, 1}` — contradicting edge-injectivity. Dual to
`rayGraph_hasOneWayEulerPath`. -/
theorem not_hasInfiniteEulerPath_rayGraph : ¬ HasInfiniteEulerPath rayGraph := by
  rintro ⟨w, hcov, hinj⟩
  -- the edge {0, 1} is traversed at some integer step t, in one of two directions
  rcases hcov 0 1 (Or.inl rfl) with ⟨t, ha, hb⟩ | ⟨t, ha, hb⟩
  · -- step t goes 0 → 1; the step INTO 0 must come from the unique neighbour 1
    have hprev := w.step_adj (t - 1)
    rw [show t - 1 + 1 = t from by ring, ha] at hprev
    rcases hprev with h | h
    · -- w.vertex (t - 1) + 1 = 0 is impossible in ℕ
      omega
    · -- h : 0 + 1 = w.vertex (t - 1), so steps t - 1 and t both traverse {0, 1}
      refine hinj (t - 1) t (by omega) (Or.inr ⟨by omega, ?_⟩)
      rw [show t - 1 + 1 = t from by ring]
  · -- step t goes 1 → 0; the step OUT of 0 must return to the unique neighbour 1
    have hnext := w.step_adj (t + 1)
    rw [hb] at hnext
    rcases hnext with h | h
    · -- h : 0 + 1 = w.vertex (t + 1 + 1), so steps t and t + 1 both traverse {0, 1}
      exact hinj t (t + 1) (by omega) (Or.inr ⟨by omega, rfl⟩)
    · -- w.vertex (t + 1 + 1) + 1 = 0 is impossible in ℕ
      omega

/-- **The line graph has no one-way Euler path.** A `ℕ`-indexed Euler walk
traverses the edge `{0, 1}` at a unique step `t`. After step `t` the walk is
trapped on one side of the cut `{…, -1, 0} | {1, 2, …}`: re-crossing would
traverse `{0, 1}` a second time. Whichever side is abandoned contains
infinitely many edges, and each of them must have been traversed at one of
the `t + 1` steps before the crossing — an injection of an infinite family
into a finite set. Dual to `lineGraph_hasInfiniteEulerPath`. -/
theorem not_hasOneWayEulerPath_lineGraph : ¬ HasOneWayEulerPath lineGraph := by
  rintro ⟨w, hcov, hinj⟩
  -- the edge {0, 1} is traversed at some step t …
  obtain ⟨t, hedge⟩ : ∃ n, (w.vertex n = 0 ∧ w.vertex (n + 1) = 1) ∨
      (w.vertex n = 1 ∧ w.vertex (n + 1) = 0) := by
    rcases hcov 0 1 (Or.inl rfl) with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact ⟨n, Or.inl hn⟩
    · exact ⟨n, Or.inr hn⟩
  -- … and at no other step (edge-injectivity)
  have huniq : ∀ i, (w.vertex i = 0 ∧ w.vertex (i + 1) = 1) ∨
      (w.vertex i = 1 ∧ w.vertex (i + 1) = 0) → i = t := by
    intro i hi
    apply hinj
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hedge with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩
    · exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
    · exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
    · exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  rcases hedge with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- crossed upward at t: from step t + 1 on, the walk stays in {1, 2, …}
    have hconf : ∀ i, t + 1 ≤ i → 1 ≤ w.vertex i := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => omega
      | succ i hti ih =>
        by_contra hlt
        push_neg at hlt
        rcases w.step_adj i with h | h
        · omega
        · exact absurd (huniq i (Or.inr ⟨by omega, by omega⟩)) (by omega)
    -- every edge {-1 - k, -k} lies in the abandoned side {…, -1, 0} …
    have hneg : ∀ k : ℕ, ∃ s,
        (w.vertex s = -1 - (k : ℤ) ∧ w.vertex (s + 1) = -(k : ℤ)) ∨
        (w.vertex s = -(k : ℤ) ∧ w.vertex (s + 1) = -1 - (k : ℤ)) := by
      intro k
      rcases hcov (-1 - (k : ℤ)) (-(k : ℤ)) (Or.inl (by ring)) with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact ⟨s, Or.inl hs⟩
      · exact ⟨s, Or.inr hs⟩
    choose f hf using hneg
    -- … so its traversal time is at most t: infinitely many edges, t + 1 slots
    have hmem : ∀ k, f k ∈ Set.Iic t := by
      intro k
      rw [Set.mem_Iic]
      by_contra hgt
      push_neg at hgt
      have := hconf (f k) (by omega)
      rcases hf k with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    have hfinj : Function.Injective f := by
      intro j k hjk
      have hj := hf j
      have hk := hf k
      rw [hjk] at hj
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    exact absurd (Set.infinite_of_injective_forall_mem hfinj hmem)
      (Set.finite_Iic t).not_infinite
  · -- crossed downward at t: from step t + 1 on, the walk stays in {…, -1, 0}
    have hconf : ∀ i, t + 1 ≤ i → w.vertex i ≤ 0 := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => omega
      | succ i hti ih =>
        by_contra hlt
        push_neg at hlt
        rcases w.step_adj i with h | h
        · exact absurd (huniq i (Or.inl ⟨by omega, by omega⟩)) (by omega)
        · omega
    -- every edge {k + 1, k + 2} lies in the abandoned side {1, 2, …} …
    have hpos : ∀ k : ℕ, ∃ s,
        (w.vertex s = (k : ℤ) + 1 ∧ w.vertex (s + 1) = (k : ℤ) + 2) ∨
        (w.vertex s = (k : ℤ) + 2 ∧ w.vertex (s + 1) = (k : ℤ) + 1) := by
      intro k
      rcases hcov ((k : ℤ) + 1) ((k : ℤ) + 2) (Or.inl (by ring)) with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact ⟨s, Or.inl hs⟩
      · exact ⟨s, Or.inr hs⟩
    choose f hf using hpos
    have hmem : ∀ k, f k ∈ Set.Iic t := by
      intro k
      rw [Set.mem_Iic]
      by_contra hgt
      push_neg at hgt
      have := hconf (f k) (by omega)
      rcases hf k with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    have hfinj : Function.Injective f := by
      intro j k hjk
      have hj := hf j
      have hk := hf k
      rw [hjk] at hj
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    exact absurd (Set.infinite_of_injective_forall_mem hfinj hmem)
      (Set.finite_Iic t).not_infinite

/-- **One-way does not imply bi-infinite**: the ray graph is a counterexample
to `HasOneWayEulerPath G → HasInfiniteEulerPath G`. -/
theorem not_oneWay_imp_biInfinite :
    ¬ ∀ (V : Type) (G : InfiniteGraph V),
      HasOneWayEulerPath G → HasInfiniteEulerPath G :=
  fun h => not_hasInfiniteEulerPath_rayGraph (h ℕ rayGraph rayGraph_hasOneWayEulerPath)

/-- **Bi-infinite does not imply one-way**: the line graph is a counterexample
to `HasInfiniteEulerPath G → HasOneWayEulerPath G`. Together with
`not_oneWay_imp_biInfinite`, the two Euler-path predicates are incomparable. -/
theorem not_biInfinite_imp_oneWay :
    ¬ ∀ (V : Type) (G : InfiniteGraph V),
      HasInfiniteEulerPath G → HasOneWayEulerPath G :=
  fun h => not_hasOneWayEulerPath_lineGraph (h ℤ lineGraph lineGraph_hasInfiniteEulerPath)

/-! ### EGW necessity: degree parity (S14)

The Erdős–Grünwald–Weiszfeld characterisation of one-way Euler paths includes
a *necessity* clause on vertex degrees: along a one-way Euler walk, every
visit to a vertex `v` other than the starting vertex consumes exactly two
edges at `v` (one arriving, one departing), so if `v` has finite degree that
degree must be **even**; the starting vertex is the sole exception — its
first visit consumes only a departing edge, so its finite degree is **odd**.

Formally, the neighbour set `{u | G.adj v u}` is counted by splitting it into

* the *out-neighbours* `w.vertex (n + 1)` over departure steps
  `n ∈ w.outSteps v` (steps with `w.vertex n = v`), and
* the *in-neighbours* `w.vertex n` over arrival steps `n ∈ w.inSteps v`
  (steps with `w.vertex (n + 1) = v`),

which are injective images (edge-injectivity), disjoint (an edge traversed
both out of and into `v` would be traversed twice), and jointly exhaustive
(the walk covers every edge at `v`). Shifting arrival steps forward by one
identifies `w.inSteps v` with `w.outSteps v \ {0}`, giving

`degree v = |outSteps v| + |outSteps v \ {0}|`,

whose parity is decided by whether `0 ∈ outSteps v`, i.e. whether `v` is the
start. Headline consequences: the odd-finite-degree vertices of a graph with
a one-way Euler path form a subsingleton, so **two distinct odd-degree
vertices rule out a one-way Euler path** — the first structural piece of the
EGW theorem. The line graph shows the parity clause alone is *not*
sufficient: it has no odd vertex at all, yet no one-way Euler path (S13) —
the number of ends enters the full characterisation. -/

namespace InfiniteWalk

/-- The steps at which the walk departs from `v` (the walk is at `v` at time
`n`, so the edge traversed at step `n` leaves `v`). Contains `0` iff `v` is
the starting vertex. -/
def outSteps {V : Type*} {G : InfiniteGraph V} (w : InfiniteWalk G) (v : V) :
    Set ℕ :=
  {n | w.vertex n = v}

/-- The steps at which the walk arrives at `v` (the walk is at `v` at time
`n + 1`, so the edge traversed at step `n` enters `v`). -/
def inSteps {V : Type*} {G : InfiniteGraph V} (w : InfiniteWalk G) (v : V) :
    Set ℕ :=
  {n | w.vertex (n + 1) = v}

/-- No step both departs from and arrives at `v`: such a step would traverse
a loop, which `InfiniteGraph.loopless` forbids. -/
theorem disjoint_outSteps_inSteps {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (v : V) : Disjoint (w.outSteps v) (w.inSteps v) := by
  rw [Set.disjoint_left]
  intro n hn hn'
  simp only [outSteps, inSteps, Set.mem_setOf_eq] at hn hn'
  exact w.step_ne n (hn.trans hn'.symm)

/-- Shifting arrival steps forward by one yields exactly the departure steps
other than `0`: the walk is at `v` at time `m ≥ 1` iff it arrived there at
time `m - 1`, and time `0` is never an arrival. -/
theorem image_succ_inSteps {V : Type*} {G : InfiniteGraph V}
    (w : InfiniteWalk G) (v : V) :
    (fun n => n + 1) '' w.inSteps v = w.outSteps v \ {0} := by
  ext m
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, inSteps,
    outSteps, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨hn, by omega⟩
  · rintro ⟨hm, h0⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    exact ⟨n, hm, rfl⟩

end InfiniteWalk

namespace IsEulerWalk

/-- The out-neighbours over departure steps and the in-neighbours over
arrival steps jointly exhaust the neighbour set of `v`: the walk covers every
edge at `v`, in one direction or the other. -/
theorem image_outSteps_union_image_inSteps {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) (v : V) :
    ((fun n => w.vertex (n + 1)) '' w.outSteps v) ∪
      ((fun n => w.vertex n) '' w.inSteps v) = {u | G.adj v u} := by
  ext u
  simp only [Set.mem_union, Set.mem_image, InfiniteWalk.outSteps,
    InfiniteWalk.inSteps, Set.mem_setOf_eq]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · rw [← hn]
      exact w.step_adj n
    · have h := w.step_adj n
      rw [hn] at h
      exact G.symm _ _ h
  · intro hu
    rcases hE.covers v u hu with ⟨n, hn1, hn2⟩ | ⟨n, hn1, hn2⟩
    · exact Or.inl ⟨n, hn1, hn2⟩
    · exact Or.inr ⟨n, hn2, hn1⟩

/-- Departure steps map injectively to out-neighbours: two departures to the
same neighbour `u` would traverse the edge `{v, u}` twice. -/
theorem injOn_vertex_succ_outSteps {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) (v : V) :
    Set.InjOn (fun n => w.vertex (n + 1)) (w.outSteps v) := by
  intro m hm n hn h
  simp only [InfiniteWalk.outSteps, Set.mem_setOf_eq] at hm hn
  exact hE.injective m n (Or.inl ⟨hm.trans hn.symm, h⟩)

/-- Arrival steps map injectively to in-neighbours: two arrivals from the
same neighbour `u` would traverse the edge `{v, u}` twice. -/
theorem injOn_vertex_inSteps {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) (v : V) :
    Set.InjOn (fun n => w.vertex n) (w.inSteps v) := by
  intro m hm n hn h
  simp only [InfiniteWalk.inSteps, Set.mem_setOf_eq] at hm hn
  exact hE.injective m n (Or.inl ⟨h, hm.trans hn.symm⟩)

/-- No neighbour of `v` is both an out-neighbour and an in-neighbour: the
edge `{v, u}` would be traversed twice (once leaving `v`, once entering it —
the two steps are distinct because no step is a loop). -/
theorem disjoint_image_outSteps_image_inSteps {V : Type*}
    {G : InfiniteGraph V} {w : InfiniteWalk G} (hE : IsEulerWalk G w)
    (v : V) :
    Disjoint ((fun n => w.vertex (n + 1)) '' w.outSteps v)
      ((fun n => w.vertex n) '' w.inSteps v) := by
  rw [Set.disjoint_left]
  rintro u ⟨m, hm, rfl⟩ ⟨n, hn, hnm⟩
  simp only [InfiniteWalk.outSteps, InfiniteWalk.inSteps,
    Set.mem_setOf_eq] at hm hn
  have hmn : m = n := hE.injective m n (Or.inr ⟨hm.trans hn.symm, hnm.symm⟩)
  subst hmn
  exact w.step_ne m (hm.trans hn.symm)

/-- If `v` has finitely many neighbours, its departure steps are finite:
they inject into the neighbour set. -/
theorem finite_outSteps {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) {v : V}
    (hfin : {u | G.adj v u}.Finite) : (w.outSteps v).Finite := by
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (hE.injOn_vertex_succ_outSteps v)
  rw [← hE.image_outSteps_union_image_inSteps v]
  exact Set.subset_union_left

/-- If `v` has finitely many neighbours, its arrival steps are finite. -/
theorem finite_inSteps {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) {v : V}
    (hfin : {u | G.adj v u}.Finite) : (w.inSteps v).Finite := by
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (hE.injOn_vertex_inSteps v)
  rw [← hE.image_outSteps_union_image_inSteps v]
  exact Set.subset_union_right

/-- **Degree census along a one-way Euler walk**: the neighbour count of a
finite-degree vertex `v` is the number of departure steps plus the number of
departure steps other than `0`. Each visit to `v` at time `m ≥ 1` pairs an
arrival (step `m - 1`) with a departure (step `m`); a visit at time `0` is an
unpaired departure. -/
theorem ncard_neighbors_eq {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) (v : V)
    (hfin : {u | G.adj v u}.Finite) :
    {u | G.adj v u}.ncard =
      (w.outSteps v).ncard + (w.outSteps v \ {0}).ncard := by
  have hOut : (w.outSteps v).Finite := hE.finite_outSteps hfin
  have hIn : (w.inSteps v).Finite := hE.finite_inSteps hfin
  calc {u | G.adj v u}.ncard
      = (((fun n => w.vertex (n + 1)) '' w.outSteps v) ∪
          ((fun n => w.vertex n) '' w.inSteps v)).ncard := by
        rw [hE.image_outSteps_union_image_inSteps v]
    _ = ((fun n => w.vertex (n + 1)) '' w.outSteps v).ncard +
          ((fun n => w.vertex n) '' w.inSteps v).ncard :=
        Set.ncard_union_eq (hE.disjoint_image_outSteps_image_inSteps v)
          (hOut.image _) (hIn.image _)
    _ = (w.outSteps v).ncard + (w.inSteps v).ncard := by
        rw [(hE.injOn_vertex_succ_outSteps v).ncard_image,
          (hE.injOn_vertex_inSteps v).ncard_image]
    _ = (w.outSteps v).ncard + (w.outSteps v \ {0}).ncard := by
        rw [← w.image_succ_inSteps v,
          Set.ncard_image_of_injective _ (add_left_injective 1)]

/-- **EGW necessity, non-start case**: along a one-way Euler walk, every
finite-degree vertex other than the starting vertex has an *even* number of
neighbours — each visit pairs one arrival with one departure. -/
theorem even_ncard_neighbors_of_ne_start {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w) {v : V}
    (hfin : {u | G.adj v u}.Finite) (hv : v ≠ w.vertex 0) :
    Even {u | G.adj v u}.ncard := by
  have h0 : (0 : ℕ) ∉ w.outSteps v := by
    simp only [InfiniteWalk.outSteps, Set.mem_setOf_eq]
    exact fun h => hv h.symm
  rw [hE.ncard_neighbors_eq v hfin, Set.sdiff_singleton_eq_self h0]
  exact ⟨(w.outSteps v).ncard, rfl⟩

/-- **EGW necessity, start case**: the starting vertex of a one-way Euler
walk, if of finite degree, has an *odd* number of neighbours — its first
departure is unpaired. -/
theorem odd_ncard_neighbors_start {V : Type*} {G : InfiniteGraph V}
    {w : InfiniteWalk G} (hE : IsEulerWalk G w)
    (hfin : {u | G.adj (w.vertex 0) u}.Finite) :
    Odd {u | G.adj (w.vertex 0) u}.ncard := by
  have h0 : (0 : ℕ) ∈ w.outSteps (w.vertex 0) := by
    simp only [InfiniteWalk.outSteps, Set.mem_setOf_eq]
  have hOut : (w.outSteps (w.vertex 0)).Finite := hE.finite_outSteps hfin
  have hpos : 0 < (w.outSteps (w.vertex 0)).ncard :=
    (Set.ncard_pos hOut).mpr ⟨0, h0⟩
  rw [hE.ncard_neighbors_eq _ hfin, Set.ncard_sdiff_singleton_of_mem h0]
  exact ⟨(w.outSteps (w.vertex 0)).ncard - 1, by omega⟩

/-- Degree form of the non-start parity theorem: the `infiniteDegree` of a
finite-degree non-start vertex is `2 * k` for some `k : ℕ`. -/
theorem infiniteDegree_eq_two_mul_of_ne_start {V : Type*}
    {G : InfiniteGraph V} {w : InfiniteWalk G} (hE : IsEulerWalk G w)
    {v : V} (hfin : infiniteDegree G v ≠ ⊤) (hv : v ≠ w.vertex 0) :
    ∃ k : ℕ, infiniteDegree G v = 2 * k := by
  have hf : {u | G.adj v u}.Finite := by
    rwa [infiniteDegree, Set.encard_ne_top_iff] at hfin
  obtain ⟨k, hk⟩ := hE.even_ncard_neighbors_of_ne_start hf hv
  refine ⟨k, ?_⟩
  rw [infiniteDegree, ← hf.cast_ncard_eq, hk]
  push_cast
  ring

/-- Degree form of the start parity theorem: the `infiniteDegree` of the
starting vertex, if finite, is `2 * k + 1` for some `k : ℕ`. -/
theorem infiniteDegree_start_eq_two_mul_add_one {V : Type*}
    {G : InfiniteGraph V} {w : InfiniteWalk G} (hE : IsEulerWalk G w)
    (hfin : infiniteDegree G (w.vertex 0) ≠ ⊤) :
    ∃ k : ℕ, infiniteDegree G (w.vertex 0) = 2 * k + 1 := by
  have hf : {u | G.adj (w.vertex 0) u}.Finite := by
    rwa [infiniteDegree, Set.encard_ne_top_iff] at hfin
  obtain ⟨k, hk⟩ := hE.odd_ncard_neighbors_start hf
  refine ⟨k, ?_⟩
  rw [infiniteDegree, ← hf.cast_ncard_eq, hk]
  push_cast
  ring

end IsEulerWalk

/-- **At most one odd vertex**: in a graph with a one-way Euler path, the
finite-degree vertices of odd degree form a subsingleton — every such vertex
coincides with the walk's starting vertex. -/
theorem oddVertices_subsingleton_of_hasOneWayEulerPath {V : Type*}
    {G : InfiniteGraph V} (h : HasOneWayEulerPath G) :
    {v | {u | G.adj v u}.Finite ∧ Odd {u | G.adj v u}.ncard}.Subsingleton := by
  obtain ⟨w, hE⟩ := h
  have key : ∀ v ∈ {v | {u | G.adj v u}.Finite ∧ Odd {u | G.adj v u}.ncard},
      v = w.vertex 0 := by
    rintro v ⟨hf, hodd⟩
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd)
      (hE.even_ncard_neighbors_of_ne_start hf hne)
  intro v₁ h₁ v₂ h₂
  rw [key v₁ h₁, key v₂ h₂]

/-- **EGW necessity — the headline obstruction**: two distinct vertices of
odd finite degree rule out a one-way Euler path. This is Euler's classical
parity obstruction (Königsberg has *four* odd vertices), transplanted to
infinite graphs. -/
theorem not_hasOneWayEulerPath_of_two_odd_vertices {V : Type*}
    {G : InfiniteGraph V} {v₁ v₂ : V} (hne : v₁ ≠ v₂)
    (h₁f : {u | G.adj v₁ u}.Finite) (h₁ : Odd {u | G.adj v₁ u}.ncard)
    (h₂f : {u | G.adj v₂ u}.Finite) (h₂ : Odd {u | G.adj v₂ u}.ncard) :
    ¬ HasOneWayEulerPath G :=
  fun h =>
    hne (oddVertices_subsingleton_of_hasOneWayEulerPath h ⟨h₁f, h₁⟩ ⟨h₂f, h₂⟩)

/-- The ray graph's vertex `0` has exactly one neighbour. -/
theorem rayGraph_neighbors_zero : {u | rayGraph.adj 0 u} = {1} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> omega
  · rintro rfl
    exact Or.inl rfl

/-- Sanity instantiation of the start-case parity theorem: the ray graph's
starting vertex `0` has odd degree (namely one), consistent with
`rayGraph_hasOneWayEulerPath` (the S12 witness `rayWalk` starts at `0`). -/
theorem rayGraph_odd_ncard_neighbors_zero :
    Odd {u | rayGraph.adj 0 u}.ncard := by
  rw [rayGraph_neighbors_zero, Set.ncard_singleton]
  exact ⟨0, by omega⟩

/-- Every vertex of the line graph has exactly the two neighbours `n ± 1`. -/
theorem lineGraph_neighbors (n : ℤ) :
    {u | lineGraph.adj n u} = {n + 1, n - 1} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> omega
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by ring)

/-- Every vertex of the line graph has even degree (namely two). -/
theorem lineGraph_even_ncard_neighbors (n : ℤ) :
    Even {u | lineGraph.adj n u}.ncard := by
  rw [lineGraph_neighbors n, Set.ncard_pair (by omega : n + 1 ≠ n - 1)]
  exact ⟨1, rfl⟩

/-- **Parity necessity is not sufficiency**: the line graph has *no* vertex
of odd degree — every vertex has exactly two neighbours — yet it has no
one-way Euler path (S13). The parity clause of the EGW characterisation is
therefore strictly weaker than the full characterisation: the number of
*ends* enters (the line has two, and a one-way walk can exhaust only one). -/
theorem lineGraph_parity_not_sufficient :
    (∀ n : ℤ, Even {u | lineGraph.adj n u}.ncard) ∧
      ¬ HasOneWayEulerPath lineGraph :=
  ⟨lineGraph_even_ncard_neighbors, not_hasOneWayEulerPath_lineGraph⟩

/-! ### EGW necessity, bi-infinite case: NO odd vertex at all (S15)

S14 established the one-way parity clause: along a ℕ-indexed Euler walk every
finite-degree vertex has even degree *except possibly the start* (which is
odd). A ℤ-indexed bi-infinite Euler walk has **no start**, and correspondingly
no exception: shifting arrival steps forward by one identifies `w.inSteps v`
with `w.outSteps v` *exactly* — over ℤ there is no unpaired index `0` — so

`degree v = 2 · |outSteps v|`,

and **every** finite-degree vertex is even. Headline: a single odd
finite-degree vertex rules out a bi-infinite Euler path. Together with S14
this completes the parity half of the incomparability picture:

* one-way: at most ONE odd vertex (the start, S14);
* bi-infinite: NO odd vertex (S15).

Sanity: the ray graph's vertex `0` has degree `1` (odd), so the parity
obstruction *re-proves* S13's `not_hasInfiniteEulerPath_rayGraph` by pure
degree counting — the S13 proof went through walk surjectivity instead. -/

namespace BiInfiniteWalk

/-- The integer steps at which the bi-infinite walk departs from `v`. -/
def outSteps {V : Type*} {G : InfiniteGraph V} (w : BiInfiniteWalk G) (v : V) :
    Set ℤ :=
  {n | w.vertex n = v}

/-- The integer steps at which the bi-infinite walk arrives at `v`. -/
def inSteps {V : Type*} {G : InfiniteGraph V} (w : BiInfiniteWalk G) (v : V) :
    Set ℤ :=
  {n | w.vertex (n + 1) = v}

/-- Each step of a bi-infinite walk traverses a non-loop edge. -/
theorem step_ne {V : Type*} {G : InfiniteGraph V}
    (w : BiInfiniteWalk G) (n : ℤ) : w.vertex n ≠ w.vertex (n + 1) :=
  fun h => G.loopless (w.vertex n) (h ▸ w.step_adj n)

/-- No integer step both departs from and arrives at `v` (no loops). -/
theorem disjoint_outSteps_inSteps {V : Type*} {G : InfiniteGraph V}
    (w : BiInfiniteWalk G) (v : V) : Disjoint (w.outSteps v) (w.inSteps v) := by
  rw [Set.disjoint_left]
  intro n hn hn'
  simp only [outSteps, inSteps, Set.mem_setOf_eq] at hn hn'
  exact w.step_ne n (hn.trans hn'.symm)

/-- **The bi-infinite pairing has no exception**: shifting arrival steps
forward by one yields *exactly* the departure steps. Over ℤ every departure
at time `m` is preceded by the step at time `m − 1` — there is no first
index, hence no unpaired departure (contrast with the ℕ-indexed
`InfiniteWalk.image_succ_inSteps`, whose image is `outSteps v \ {0}`). -/
theorem image_succ_inSteps {V : Type*} {G : InfiniteGraph V}
    (w : BiInfiniteWalk G) (v : V) :
    (fun n : ℤ => n + 1) '' w.inSteps v = w.outSteps v := by
  ext m
  simp only [Set.mem_image, inSteps, outSteps, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hn
  · intro hm
    exact ⟨m - 1, by simpa using hm, by ring⟩

end BiInfiniteWalk

namespace IsBiInfiniteEulerWalk

/-- A bi-infinite Euler walk covers each adjacent pair. -/
theorem covers {V : Type*} {G : InfiniteGraph V} {w : BiInfiniteWalk G}
    (hE : IsBiInfiniteEulerWalk G w) (u v : V) (hadj : G.adj u v) :
    w.CoversEdge u v :=
  hE.1 u v hadj

/-- Edge-injectivity of a bi-infinite Euler walk in the positive form used by
the census: two step indices traversing the same undirected edge coincide. -/
theorem injective {V : Type*} {G : InfiniteGraph V} {w : BiInfiniteWalk G}
    (hE : IsBiInfiniteEulerWalk G w) (m n : ℤ)
    (h : (w.vertex m = w.vertex n ∧ w.vertex (m + 1) = w.vertex (n + 1)) ∨
      (w.vertex m = w.vertex (n + 1) ∧ w.vertex (m + 1) = w.vertex n)) :
    m = n := by
  by_contra hmn
  exact hE.2 m n hmn h

/-- The out-neighbours over departure steps and in-neighbours over arrival
steps jointly exhaust the neighbour set of `v`. -/
theorem image_outSteps_union_image_inSteps {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) (v : V) :
    ((fun n : ℤ => w.vertex (n + 1)) '' w.outSteps v) ∪
      ((fun n : ℤ => w.vertex n) '' w.inSteps v) = {u | G.adj v u} := by
  ext u
  simp only [Set.mem_union, Set.mem_image, BiInfiniteWalk.outSteps,
    BiInfiniteWalk.inSteps, Set.mem_setOf_eq]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · rw [← hn]
      exact w.step_adj n
    · have h := w.step_adj n
      rw [hn] at h
      exact G.symm _ _ h
  · intro hu
    rcases hE.covers v u hu with ⟨n, hn1, hn2⟩ | ⟨n, hn1, hn2⟩
    · exact Or.inl ⟨n, hn1, hn2⟩
    · exact Or.inr ⟨n, hn2, hn1⟩

/-- Departure steps map injectively to out-neighbours. -/
theorem injOn_vertex_succ_outSteps {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) (v : V) :
    Set.InjOn (fun n : ℤ => w.vertex (n + 1)) (w.outSteps v) := by
  intro m hm n hn h
  simp only [BiInfiniteWalk.outSteps, Set.mem_setOf_eq] at hm hn
  exact hE.injective m n (Or.inl ⟨hm.trans hn.symm, h⟩)

/-- Arrival steps map injectively to in-neighbours. -/
theorem injOn_vertex_inSteps {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) (v : V) :
    Set.InjOn (fun n : ℤ => w.vertex n) (w.inSteps v) := by
  intro m hm n hn h
  simp only [BiInfiniteWalk.inSteps, Set.mem_setOf_eq] at hm hn
  exact hE.injective m n (Or.inl ⟨h, hm.trans hn.symm⟩)

/-- No neighbour of `v` is both an out-neighbour and an in-neighbour. -/
theorem disjoint_image_outSteps_image_inSteps {V : Type*}
    {G : InfiniteGraph V} {w : BiInfiniteWalk G}
    (hE : IsBiInfiniteEulerWalk G w) (v : V) :
    Disjoint ((fun n : ℤ => w.vertex (n + 1)) '' w.outSteps v)
      ((fun n : ℤ => w.vertex n) '' w.inSteps v) := by
  rw [Set.disjoint_left]
  rintro u ⟨m, hm, rfl⟩ ⟨n, hn, hnm⟩
  simp only [BiInfiniteWalk.outSteps, BiInfiniteWalk.inSteps,
    Set.mem_setOf_eq] at hm hn
  have hmn : m = n := hE.injective m n (Or.inr ⟨hm.trans hn.symm, hnm.symm⟩)
  subst hmn
  exact w.step_ne m (hm.trans hn.symm)

/-- If `v` has finitely many neighbours, its departure steps are finite. -/
theorem finite_outSteps {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) {v : V}
    (hfin : {u | G.adj v u}.Finite) : (w.outSteps v).Finite := by
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (hE.injOn_vertex_succ_outSteps v)
  rw [← hE.image_outSteps_union_image_inSteps v]
  exact Set.subset_union_left

/-- If `v` has finitely many neighbours, its arrival steps are finite. -/
theorem finite_inSteps {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) {v : V}
    (hfin : {u | G.adj v u}.Finite) : (w.inSteps v).Finite := by
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (hE.injOn_vertex_inSteps v)
  rw [← hE.image_outSteps_union_image_inSteps v]
  exact Set.subset_union_right

/-- **Degree census along a bi-infinite Euler walk**: the neighbour count of
a finite-degree vertex is exactly *twice* its number of departure steps —
every departure at time `m` pairs with the arrival at time `m − 1`, with no
exception (contrast the one-way census `InfiniteWalk` version, where step `0`
is unpaired). -/
theorem ncard_neighbors_eq {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) (v : V)
    (hfin : {u | G.adj v u}.Finite) :
    {u | G.adj v u}.ncard = 2 * (w.outSteps v).ncard := by
  have hOut : (w.outSteps v).Finite := hE.finite_outSteps hfin
  have hIn : (w.inSteps v).Finite := hE.finite_inSteps hfin
  have hshift : (w.inSteps v).ncard = (w.outSteps v).ncard := by
    rw [← w.image_succ_inSteps v,
      Set.ncard_image_of_injective _ (add_left_injective (1 : ℤ))]
  calc {u | G.adj v u}.ncard
      = (((fun n : ℤ => w.vertex (n + 1)) '' w.outSteps v) ∪
          ((fun n : ℤ => w.vertex n) '' w.inSteps v)).ncard := by
        rw [hE.image_outSteps_union_image_inSteps v]
    _ = ((fun n : ℤ => w.vertex (n + 1)) '' w.outSteps v).ncard +
          ((fun n : ℤ => w.vertex n) '' w.inSteps v).ncard :=
        Set.ncard_union_eq (hE.disjoint_image_outSteps_image_inSteps v)
          (hOut.image _) (hIn.image _)
    _ = (w.outSteps v).ncard + (w.inSteps v).ncard := by
        rw [(hE.injOn_vertex_succ_outSteps v).ncard_image,
          (hE.injOn_vertex_inSteps v).ncard_image]
    _ = 2 * (w.outSteps v).ncard := by
        rw [hshift]
        ring

/-- **EGW necessity, bi-infinite case**: along a bi-infinite Euler walk,
EVERY finite-degree vertex has an even number of neighbours — there is no
start, hence no exception. -/
theorem even_ncard_neighbors {V : Type*} {G : InfiniteGraph V}
    {w : BiInfiniteWalk G} (hE : IsBiInfiniteEulerWalk G w) (v : V)
    (hfin : {u | G.adj v u}.Finite) :
    Even {u | G.adj v u}.ncard := by
  rw [hE.ncard_neighbors_eq v hfin]
  exact ⟨(w.outSteps v).ncard, by ring⟩

/-- Degree form: the `infiniteDegree` of any finite-degree vertex along a
bi-infinite Euler walk is `2 * k` for some `k : ℕ`. -/
theorem infiniteDegree_eq_two_mul {V : Type*}
    {G : InfiniteGraph V} {w : BiInfiniteWalk G}
    (hE : IsBiInfiniteEulerWalk G w) {v : V}
    (hfin : infiniteDegree G v ≠ ⊤) :
    ∃ k : ℕ, infiniteDegree G v = 2 * k := by
  have hf : {u | G.adj v u}.Finite := by
    rwa [infiniteDegree, Set.encard_ne_top_iff] at hfin
  obtain ⟨k, hk⟩ := hE.even_ncard_neighbors v hf
  refine ⟨k, ?_⟩
  rw [infiniteDegree, ← hf.cast_ncard_eq, hk]
  push_cast
  ring

end IsBiInfiniteEulerWalk

/-- **No odd vertex at all**: a graph with a bi-infinite Euler path has no
finite-degree vertex of odd degree. Sharper than the one-way clause (S14
allows one odd vertex, the start). -/
theorem noOddVertex_of_hasInfiniteEulerPath {V : Type*}
    {G : InfiniteGraph V} (h : HasInfiniteEulerPath G) :
    ∀ v, {u | G.adj v u}.Finite → Even {u | G.adj v u}.ncard := by
  obtain ⟨w, hE⟩ := h
  exact fun v hf => hE.even_ncard_neighbors v hf

/-- **EGW necessity, bi-infinite headline**: a single vertex of odd finite
degree rules out a bi-infinite Euler path. -/
theorem not_hasInfiniteEulerPath_of_odd_vertex {V : Type*}
    {G : InfiniteGraph V} {v : V} (hf : {u | G.adj v u}.Finite)
    (hodd : Odd {u | G.adj v u}.ncard) :
    ¬ HasInfiniteEulerPath G :=
  fun h => Nat.not_even_iff_odd.mpr hodd (noOddVertex_of_hasInfiniteEulerPath h v hf)

/-- The parity obstruction *re-proves* S13's impossibility for the ray graph
by pure degree counting: vertex `0` has degree `1` (odd), so no bi-infinite
Euler path exists. (The S13 proof `not_hasInfiniteEulerPath_rayGraph` argued
via walk surjectivity onto arcs instead — two independent mechanisms, one
obstruction.) -/
theorem not_hasInfiniteEulerPath_rayGraph_parity :
    ¬ HasInfiniteEulerPath rayGraph :=
  not_hasInfiniteEulerPath_of_odd_vertex
    (by rw [rayGraph_neighbors_zero]; exact Set.finite_singleton 1)
    rayGraph_odd_ncard_neighbors_zero

/-- The combined S14+S15 parity picture, in one statement: a one-way Euler
path allows at most one odd finite-degree vertex, a bi-infinite Euler path
allows none. -/
theorem parity_picture {V : Type*} (G : InfiniteGraph V) :
    (HasOneWayEulerPath G →
      {v | {u | G.adj v u}.Finite ∧ Odd {u | G.adj v u}.ncard}.Subsingleton) ∧
    (HasInfiniteEulerPath G →
      {v | {u | G.adj v u}.Finite ∧ Odd {u | G.adj v u}.ncard} = ∅) := by
  refine ⟨oddVertices_subsingleton_of_hasOneWayEulerPath, fun h => ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hf hodd
  exact Nat.not_even_iff_odd.mpr hodd (noOddVertex_of_hasInfiniteEulerPath h v hf)

#check @BiInfiniteWalk.image_succ_inSteps
#check @IsBiInfiniteEulerWalk.ncard_neighbors_eq
#check @IsBiInfiniteEulerWalk.even_ncard_neighbors
#check @not_hasInfiniteEulerPath_of_odd_vertex
#check @not_hasInfiniteEulerPath_rayGraph_parity
#check @parity_picture

end KonigsbergOQ03
