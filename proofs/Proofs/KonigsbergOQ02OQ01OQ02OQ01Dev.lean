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

/-- **A trail into an even-degree vertex, from a different start, has an unused
incident edge.**
Let `p : G.Walk u v` be a trail with `u ≠ v` and `Even (G.degree v)`. Then some edge
incident to `v` is *not* used by `p`. This is the quantitative heart of Hierholzer's
"a maximal trail is closed" step: while a trail sits at a non-start vertex `v`, it has
consumed an **odd** number of `v`'s incident edges (`IsTrail.even_countP_edges_iff`),
but `v` has an **even** number in total, so an unused one always remains to extend
along. -/
theorem exists_unused_incident_edge_at_endpoint
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (hne : u ≠ v)
    (heven : Even (G.degree v)) :
    ∃ e ∈ G.incidenceFinset v, e ∉ p.edges := by
  classical
  -- The walk-edges incident to `v`, as a nodup list.
  set L : List (Sym2 V) := p.edges.filter (fun e => v ∈ e) with hLdef
  have hpnodup : p.edges.Nodup := hp.edges_nodup
  have hLnodup : L.Nodup := hpnodup.filter _
  -- Their number is odd, by the trail parity invariant applied at `x = v`.
  have hcountodd : Odd (p.edges.countP (fun e => v ∈ e)) := by
    rw [← Nat.not_even_iff_odd, hp.even_countP_edges_iff]
    intro h
    exact (h hne).2 rfl
  have hLlen : L.length = p.edges.countP (fun e => v ∈ e) := by
    rw [hLdef]; exact List.countP_eq_length_filter.symm
  have hLcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLnodup
  have hLcardodd : Odd L.toFinset.card := by rw [hLcard, hLlen]; exact hcountodd
  -- Used incident edges sit inside the incidence finset of `v`.
  have hsub : L.toFinset ⊆ G.incidenceFinset v := by
    intro e he
    rw [List.mem_toFinset, hLdef, List.mem_filter] at he
    obtain ⟨hmem, hv⟩ := he
    have hv' : v ∈ e := by simpa using hv
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨p.edges_subset_edgeSet hmem, hv'⟩
  -- Total incident edges = degree, which is even.
  have hAcard : (G.incidenceFinset v).card = G.degree v := G.card_incidenceFinset_eq_degree v
  have hAeven : Even (G.incidenceFinset v).card := by rw [hAcard]; exact heven
  -- Different parities ⇒ the used set is a *proper* subset.
  have hne_sets : L.toFinset ≠ G.incidenceFinset v := by
    intro hEq
    rw [hEq] at hLcardodd
    exact (Nat.not_even_iff_odd.mpr hLcardodd) hAeven
  have hss : L.toFinset ⊂ G.incidenceFinset v :=
    (Finset.ssubset_iff_subset_ne).mpr ⟨hsub, hne_sets⟩
  obtain ⟨e, heIn, heOut⟩ := Finset.exists_of_ssubset hss
  refine ⟨e, heIn, ?_⟩
  -- If `e` were used, it would be a used incident edge, i.e. in `L.toFinset`.
  intro hused
  apply heOut
  have hv : v ∈ e := by
    rw [SimpleGraph.mem_incidenceFinset] at heIn
    exact heIn.2
  rw [List.mem_toFinset, hLdef, List.mem_filter]
  exact ⟨hused, by simpa using hv⟩

/-- **A maximal trail is closed (undirected Hierholzer core).**
If `p : G.Walk u v` is a trail, every vertex has even degree, and `v` is *edge-maximal*
— every edge incident to `v` is already used by `p` — then `p` is closed: `u = v`.
Contrapositive of `exists_unused_incident_edge_at_endpoint`: a trail can only get stuck
back at its start. This is the step that turns "grow a trail greedily" into "obtain a
closed circuit," the inductive engine of Hierholzer's construction. -/
theorem eq_of_isTrail_edgeMaximal
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (heven : Even (G.degree v))
    (hmax : ∀ e ∈ G.incidenceFinset v, e ∈ p.edges) :
    u = v := by
  by_contra hne
  obtain ⟨e, hmem, hnot⟩ := exists_unused_incident_edge_at_endpoint hp hne heven
  exact hnot (hmax e hmem)

/-- **A closed trail uses an even number of edges incident to every vertex.**
For a *closed* trail `p : G.Walk u u`, the number of edges of `p` incident to any
vertex `x` is even. This is the parity ingredient of Hierholzer's edge-removal step
(Sub-lemma B): deleting a closed trail's edges changes each vertex's degree by an even
amount, so the "every vertex has even degree" invariant survives the induction.

The proof specializes `SimpleGraph.Walk.IsTrail.even_countP_edges_iff` at a closed
trail: its right-hand side `(u ≠ u → x ≠ u ∧ x ≠ u)` is vacuously true because
`u ≠ u` is false, so the incident-edge count is even with no hypothesis on `x`.
Contrast `exists_unused_incident_edge_at_endpoint`, where the *open* case (`u ≠ v`)
forces the count at `v` to be odd. -/
theorem even_countP_edges_of_closed
    {u : V} {p : G.Walk u u} (hp : p.IsTrail) (x : V) :
    Even (p.edges.countP (fun e => x ∈ e)) := by
  rw [hp.even_countP_edges_iff]
  intro huu
  exact absurd rfl huu

/-- **Deleting a closed trail's edges preserves the all-even-degree invariant (Sub-lemma B).**
Let `p : G.Walk u u` be a closed trail in a graph where every vertex has even degree.
Then in `G.deleteEdges p.edges.toFinset` every vertex *still* has even degree.

This is the induction-step hypothesis-preservation lemma of Hierholzer's construction:
after extracting a closed circuit and removing its edges, the residual graph again
satisfies "every vertex has even degree", so the strong induction on edge count applies
to it. The proof combines two evens: the incident-edge count of `x` in the deleted graph
is `#(G.incidenceFinset x) - #(A ∩ S)` where `A = G.incidenceFinset x`, `S = p.edges`;
`#A = G.degree x` is even by hypothesis, and `#(A ∩ S)` — the edges of `p` incident to
`x` — is even by `even_countP_edges_of_closed`. A difference of evens (with the subtracted
set a subset) is even. -/
theorem even_degree_deleteEdges_of_closed_trail
    [Fintype V] [DecidableRel G.Adj]
    {u : V} {p : G.Walk u u} (hp : p.IsTrail)
    (heven : ∀ x, Even (G.degree x)) (x : V) :
    Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
  classical
  set S : Finset (Sym2 V) := p.edges.toFinset with hSdef
  set A : Finset (Sym2 V) := G.incidenceFinset x with hAdef
  -- The incident edges of `x` surviving deletion are exactly `A \ S`.
  have hInc : (G.deleteEdges (S : Set (Sym2 V))).incidenceFinset x = A \ S := by
    rw [hAdef, incidenceFinset_eq_filter, incidenceFinset_eq_filter, edgeFinset_deleteEdges]
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  -- Rewrite the deleted-graph degree as the cardinality of its surviving incidence set.
  rw [← card_incidenceFinset_eq_degree, hInc]
  -- `(A \ S).card + (A ∩ S).card = A.card`.
  have hsplit : (A \ S).card + (A ∩ S).card = A.card :=
    Finset.card_sdiff_add_card_inter A S
  -- `A.card = G.degree x` is even.
  have hAeven : Even A.card := by rw [hAdef, card_incidenceFinset_eq_degree]; exact heven x
  -- `(A ∩ S).card` counts `p`'s edges incident to `x`; equals `countP`, which is even.
  have hInterEven : Even (A ∩ S).card := by
    -- `A ∩ S = (p.edges.filter (x ∈ ·)).toFinset`, whose card is the nodup filter length.
    have hcard : (A ∩ S).card = p.edges.countP (fun e => x ∈ e) := by
      have hfilter : A ∩ S = (p.edges.filter (fun e => x ∈ e)).toFinset := by
        rw [hAdef, hSdef, incidenceFinset_eq_filter]
        ext e
        simp only [Finset.mem_inter, Finset.mem_filter, List.mem_toFinset, List.mem_filter,
          mem_edgeFinset, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨_, hx⟩, hmem⟩; exact ⟨hmem, hx⟩
        · rintro ⟨hmem, hx⟩; exact ⟨⟨p.edges_subset_edgeSet hmem, hx⟩, hmem⟩
      rw [hfilter, List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
      exact List.countP_eq_length_filter.symm
    rw [hcard]; exact even_countP_edges_of_closed hp x
  -- Sum of the two parts is `A.card`, both `(A ∩ S).card` and `A.card` even ⇒ `(A \ S).card` even.
  obtain ⟨a, ha⟩ := hAeven
  obtain ⟨b, hb⟩ := hInterEven
  rw [ha] at hsplit
  rw [hb] at hsplit
  refine ⟨a - b, ?_⟩
  omega

end UndirectedEulerDev
