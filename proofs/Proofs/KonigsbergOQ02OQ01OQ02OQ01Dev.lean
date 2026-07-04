/-
# Undirected Hierholzer — development scaffolding (base case)

Companion development file for `KonigsbergOQ02OQ01OQ02OQ01.lean`, whose main
theorem `undirected_euler_circuit_sufficient` (the undirected Hierholzer
sufficiency direction) still carries a single `sorry`.

Mathlib provides the *necessity* direction only
(`SimpleGraph.Walk.IsEulerian.even_degree_iff`,
`SimpleGraph.Walk.IsEulerian.card_odd_degree`); it has **no** existence/Hierholzer
construction, so sufficiency must be built natively in the `SimpleGraph.Walk` API.
The `Digraph`-based directed proof in `KonigsbergOQ02OQ01.lean` is **not** reusable
here: it is built on a bespoke `Digraph` structure with its own `Walk`, `splice`,
`removeArcList` and `arcCount`, none of which are `SimpleGraph.Walk` objects.

The standard proof is strong induction on `G.edgeFinset.card`. This file discharges
the **base case** natively (0 edges ⇒ the trivial `nil` walk is Eulerian); the
remaining inductive core (a maximal trail is closed, edge-removal preserves the
all-even-degree invariant, and connectivity lets residual circuits splice in) is the
~600–1000 line classical construction still to be built or delegated.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEulerDev

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- **Base case of the undirected Hierholzer induction.**
A connected simple graph with no edges has an Eulerian circuit: the trivial `nil`
walk at any of its vertices. Mathlib defines `p.IsEulerian` as
`∀ e ∈ G.edgeSet, p.edges.count e = 1`, which holds vacuously here since `G` has no
edges. -/
theorem euler_circuit_of_edgeSet_empty
    (hconn : G.Connected) (hE : G.edgeSet = ∅) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  obtain ⟨u⟩ := hconn.nonempty
  refine ⟨u, Walk.nil, ?_⟩
  -- `IsEulerian` unfolds to `∀ e ∈ G.edgeSet, ...`; vacuous as there are no edges.
  intro e he
  rw [hE] at he
  exact absurd he (Set.notMem_empty e)

/-- **Hierholzer's continuation invariant.**
In a *nontrivial* connected simple graph in which every vertex has even degree, every
vertex has degree at least `2`.

This is the structural fact underpinning the "a maximal trail is closed" step of the
undirected Hierholzer induction. When a trail arrives at a vertex `v ≠ start` it has
used an *odd* number of `v`'s incident edges (one on each earlier visit plus the edge
just traversed); since `G.degree v` is even there is always an unused incident edge to
continue along, so a trail can only get *stuck* — become maximal — back at its start
vertex, i.e. it is closed. The `2 ≤ G.degree v` bound below is the base quantitative
form of that parity slack: a positive even number is at least `2`.

`Nontrivial V` is necessary: the one-vertex connected graph has `G.degree v = 0`. In
the induction this hypothesis holds in exactly the inductive (edge-containing) case;
the edgeless base case is handled by `euler_circuit_of_edgeSet_empty` above. -/
theorem two_le_degree_of_even_of_connected
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) (v : V) :
    2 ≤ G.degree v := by
  have hpos : 0 < G.degree v := hconn.preconnected.degree_pos_of_nontrivial v
  obtain ⟨k, hk⟩ := heven v
  omega

end UndirectedEulerDev
