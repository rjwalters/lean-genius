/-
# Undirected Hierholzer — Bridge lemma: a partial closed trail has a boundary edge

Companion development file for `KonigsbergOQ02OQ01OQ02OQ01.lean`, whose main theorem
`undirected_euler_circuit_sufficient` (the undirected Hierholzer sufficiency
direction) still carries a single `sorry`. The standard proof is strong induction on
`G.edgeFinset.card`, and its three structural ingredients are already verified:

* **Sub-lemma A** — a maximal trail is closed (`eq_of_isTrail_edgeMaximal`, `Dev`).
* **Sub-lemma B** — deleting a closed trail's edges preserves all-even-degree (#34714).
* **Sub-lemma C** — splicing a residual sub-circuit into a closed trail (#34731,
  `Splice`).

The inductive step needs one more glue fact, supplied here: whenever a closed trail
`c` fails to be Eulerian (it misses at least one edge of a *connected* `G`), the missing
edge cannot be "far away" — connectivity forces a **boundary edge**: an edge of `G` that
is unused by `c` yet incident to a vertex lying on `c.support`. This is exactly the
vertex `w ∈ c.support` at which the residual Eulerian sub-circuit (obtained from the
induction hypothesis on `G.deleteEdges c.edges`) is spliced back in via
`exists_isTrail_splice_of_mem_support`.

The proof is the classical connectivity argument: were *every* edge incident to
`c.support` already used by `c`, then `c.support` would be closed under adjacency (a used
edge keeps both its endpoints on the support, `snd_mem_support_of_mem_edges`); being
nonempty (`u` is on it) and `G` connected, it would then be all of `V`; but then the
missing edge, having an endpoint in `V = c.support`, would itself be incident to the
support and hence used — a contradiction.

Depends only on Mathlib's `SimpleGraph.Walk`/connectivity API (0 sorries, 0 new
axioms); it is kept in its own file to avoid edit conflicts with the parallel `Dev` and
`Splice` development.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEulerBoundary

variable {V : Type*} {G : SimpleGraph V}

/-- **Adjacency-closed predicates are walk-closed.**
If a vertex predicate `P` is closed under taking neighbours (whenever `P w` and
`G.Adj w x` then `P x`), then it is closed along entire walks: any walk starting at a
vertex satisfying `P` ends at a vertex satisfying `P`. Structural recursion on the walk.

Stated for an arbitrary predicate `P : V → Prop` (rather than a `Set V`) so it applies
directly to `fun v => v ∈ c.support`, whose membership is `List` membership. -/
theorem forall_walk_of_adjClosed {P : V → Prop}
    (hcl : ∀ ⦃w x : V⦄, P w → G.Adj w x → P x) :
    ∀ {a b : V}, G.Walk a b → P a → P b
  | _, _, Walk.nil, ha => ha
  | _, _, Walk.cons h q, ha => forall_walk_of_adjClosed hcl q (hcl ha h)

/-- **A nonempty adjacency-closed predicate in a connected graph holds everywhere.**
If `G` is connected, `P` is closed under adjacency, and `P` holds at some vertex `a`,
then `P` holds at every vertex: each `v` is reachable from `a` by a walk, and walks
preserve `P` by `forall_walk_of_adjClosed`. -/
theorem forall_of_adjClosed (hconn : G.Connected) {P : V → Prop}
    (hcl : ∀ ⦃w x : V⦄, P w → G.Adj w x → P x) {a : V} (ha : P a) :
    ∀ v, P v := by
  intro v
  obtain ⟨p⟩ := hconn.preconnected a v
  exact forall_walk_of_adjClosed hcl p ha

/-- **Boundary edge for a non-Eulerian closed trail (Hierholzer bridge lemma).**
Let `G` be connected and let `c : G.Walk u u` be a walk that misses at least one edge of
`G` (`hmiss`). Then some edge of `G` unused by `c` is incident to a vertex of
`c.support`: there exist `w ∈ c.support` and a neighbour `x` with `G.Adj w x` and
`s(w, x) ∉ c.edges`.

This is the vertex at which the residual Eulerian sub-circuit is spliced into `c` in the
inductive step of the undirected Hierholzer proof. Axiom-free, no `sorry`. -/
theorem exists_boundary_edge_of_missing
    (hconn : G.Connected) {u : V} {c : G.Walk u u}
    (hmiss : ∃ e ∈ G.edgeSet, e ∉ c.edges) :
    ∃ w x : V, w ∈ c.support ∧ G.Adj w x ∧ s(w, x) ∉ c.edges := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ w x, w ∈ c.support → G.Adj w x → s(w, x) ∈ c.edges`.
  -- The support of `c` is then closed under adjacency: a used edge keeps both endpoints
  -- on the support (`snd_mem_support_of_mem_edges`).
  have hcl : ∀ ⦃w x : V⦄, w ∈ c.support → G.Adj w x → x ∈ c.support := by
    intro w x hw hadj
    exact snd_mem_support_of_mem_edges c (hcon w x hw hadj)
  -- Hence, `G` being connected and `u ∈ c.support`, the support is all of `V`.
  have hall : ∀ v, v ∈ c.support :=
    forall_of_adjClosed hconn hcl c.start_mem_support
  -- The missing edge has an endpoint in `V = c.support`, so it is incident to the support
  -- and therefore used — contradicting that it is missing.
  obtain ⟨e, heG, hec⟩ := hmiss
  induction e using Sym2.ind with
  | _ a b =>
    -- `s(a, b) ∈ G.edgeSet` is definitionally `G.Adj a b` (`mem_edgeSet` is `Iff.rfl`).
    have hadj : G.Adj a b := heG
    exact hec (hcon a b (hall a) hadj)

end UndirectedEulerBoundary
