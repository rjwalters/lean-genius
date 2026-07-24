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

end KonigsbergOQ03
