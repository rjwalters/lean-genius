/-
# Undirected Eulerian Circuit Theorem — Degree Characterization (Sufficiency)

This file states and (via Aristotle proof search) aims to prove the **sufficiency**
half of Euler's theorem on Eulerian circuits for *undirected* simple graphs — the
undirected **Hierholzer** direction:

> If a finite, connected undirected simple graph `G` has every vertex of even
> degree, then `G` has an Eulerian circuit (a closed trail using every edge
> exactly once).

Together with the **necessity** results in `KonigsbergOQ02OQ01OQ02.lean`
(`eulerian_circuit_forall_even`) this completes Euler's characterization:

* `G` (connected) has an Eulerian **circuit** iff every vertex has **even** degree.

## Relationship to the directed case

The *directed* analogue is fully machine-checked in `KonigsbergOQ02OQ01.lean`
(`directed_euler_circuit_sufficient_corrected`, 0 sorries), built from a splice
constructor, an arc-removal operation preserving balance, and the key sub-lemma
`maximal_balanced_trail_is_circuit`.

**Note on why the naive reduction fails.** One might hope to reduce the undirected
theorem to the directed one by replacing every undirected edge `{u,v}` with the two
directed arcs `(u,v)` and `(v,u)`. The resulting digraph is balanced
(in-degree = out-degree = undirected degree) and strongly connected, so the directed
theorem yields a directed Eulerian circuit. But that circuit traverses each
undirected edge **twice** (once in each direction), so it is *not* an undirected
Eulerian circuit. A native undirected Hierholzer argument is therefore required,
mirroring the directed sub-lemma structure:

1. from an even-degree graph, any maximal trail from a vertex is closed (the
   current endpoint always has an unused incident edge by a parity/handshake count);
2. removing the edges of a closed trail preserves the all-even-degree property;
3. splice a residual closed trail (through a shared vertex, which exists by
   connectivity) into the main circuit; induct on the number of edges.

The undirected book-keeping differs from the directed case because incidence is
symmetric: the relevant parity invariant is `Even (G.degree v)` rather than the
`inDegree = outDegree` balance condition.

## Status

The main theorem currently carries a single `sorry` and is submitted to Aristotle
for proof search as a KNOWN classical result. The statement is pinned here so the
gallery entry can track progress and integrate a completed proof.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEuler

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **Sufficiency for Eulerian circuits (undirected Hierholzer).**
A finite, connected undirected simple graph in which every vertex has even degree
possesses an Eulerian circuit: a closed walk using every edge exactly once.

This is the converse of `eulerian_circuit_forall_even` (in
`KonigsbergOQ02OQ01OQ02.lean`); together they give Euler's full characterization of
Eulerian circuits for connected undirected graphs. -/
theorem undirected_euler_circuit_sufficient
    (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  sorry

/-- **Euler's characterization of Eulerian circuits (undirected).**
For a connected undirected simple graph, an Eulerian circuit exists iff every vertex
has even degree. Combines the necessity direction with the sufficiency direction
above. -/
theorem undirected_euler_circuit_iff (hconn : G.Connected) :
    (∃ (u : V) (p : G.Walk u u), p.IsEulerian) ↔ (∀ v, Even (G.degree v)) := by
  constructor
  · rintro ⟨u, p, hp⟩ x
    -- necessity: an Eulerian circuit forces every degree even
    rw [hp.even_degree_iff]
    intro huu
    exact absurd rfl huu
  · intro heven
    exact undirected_euler_circuit_sufficient hconn heven

end UndirectedEuler
