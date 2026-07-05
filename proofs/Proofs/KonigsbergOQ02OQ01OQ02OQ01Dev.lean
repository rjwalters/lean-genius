/-
# Undirected Hierholzer — native `SimpleGraph.Walk` development (COMPLETE)

Companion development file for `KonigsbergOQ02OQ01OQ02OQ01.lean`. It now supplies a
**complete, 0-sorry** proof of the undirected Hierholzer sufficiency direction; the
main theorem `undirected_euler_circuit_sufficient` there delegates to
`undirected_euler_circuit_sufficient'` below.

Mathlib provides the *necessity* direction only
(`SimpleGraph.Walk.IsEulerian.even_degree_iff`,
`SimpleGraph.Walk.IsEulerian.card_odd_degree`); it has **no** existence/Hierholzer
construction, so sufficiency is built natively in the `SimpleGraph.Walk` API here.
The `Digraph`-based directed proof in `KonigsbergOQ02OQ01.lean` is **not** reusable:
it is built on a bespoke `Digraph` structure with its own `Walk`, `splice`,
`removeArcList` and `arcCount`, none of which are `SimpleGraph.Walk` objects.

This file assembles the sufficiency proof from:
* the **base case** (0 edges ⇒ the trivial `nil` walk is Eulerian);
* Sub-lemma A (`eq_of_isTrail_edgeMaximal`): an edge-maximal trail is closed;
* Sub-lemma B (`even_degree_deleteEdges_of_closed_trail`): edge removal preserves the
  all-even-degree invariant (kept for the alternate induction route, off the critical
  path of the extremal argument);
* Sub-lemma C (the four `exists_max_length_trail` … `undirected_euler_circuit_sufficient'`
  theorems): the **extremal** argument — a maximum-length trail is closed (Step 1) and
  Eulerian (Step 2, via `exists_boundary_dart` + `rotate` + `concat`) — which needs
  neither strong induction on edge count nor Sub-lemma B.
All checked against `leanprover/lean4:v4.26.0` Mathlib.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
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

/-- **Extracting a maximal trail preserves the all-even-degree invariant.**
Package the two halves of the Hierholzer induction step into the shape the recursion
actually consumes. In the greedy phase we grow a trail `p : G.Walk u v` until it is
*edge-maximal* at its current endpoint `v` (every edge incident to `v` is already used).
Sub-lemma A (`eq_of_isTrail_edgeMaximal`) shows such a maximal trail is automatically
**closed** (`u = v`), so the extracted circuit is a genuine closed trail; Sub-lemma B
(`even_degree_deleteEdges_of_closed_trail`) then shows deleting its edges leaves every
vertex with even degree. Hence the residual graph `G.deleteEdges p.edges.toFinset`
re-satisfies "every vertex has even degree" — exactly the hypothesis the strong
induction on edge count needs to recurse into it, *without* the caller having to know in
advance that the maximal trail closed up. This is the invariant-preservation obligation
of the induction step, discharged directly from `heven` and edge-maximality. -/
theorem even_degree_deleteEdges_of_maximal_trail
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (heven : ∀ x, Even (G.degree x))
    (hmax : ∀ e ∈ G.incidenceFinset v, e ∈ p.edges) (x : V) :
    Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
  -- A maximal trail is closed: its start equals its (maximal) endpoint.
  obtain rfl : u = v := eq_of_isTrail_edgeMaximal hp (heven v) hmax
  -- Now `p : G.Walk u u` is a closed trail; Sub-lemma B applies verbatim.
  exact even_degree_deleteEdges_of_closed_trail hp heven x

/-! ### Sub-lemma C (undirected Hierholzer sufficiency) — EXTREMAL proof.

Rather than the residual-graph induction (extract closed trail, delete edges via
Sub-lemma B, recurse, splice), take a trail of **maximum** length. It is closed
(Step 1, via Sub-lemma A) and Eulerian (Step 2, via a boundary-crossing dart +
rotate + concat). This route needs neither induction nor Sub-lemma B. -/

/-- Among all trails of `G` (any endpoints) there is one of maximum length.
Formulated over the `Set ℕ` of achievable lengths, closed by `Nat.sSup_mem` /
`le_csSup`; the a-priori bound is Mathlib's `IsTrail.length_le_card_edgeFinset`. -/
theorem exists_max_length_trail
    [Fintype V] [DecidableRel G.Adj] [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧
      ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length := by
  classical
  have hTne :
      {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}.Nonempty := by
    obtain ⟨w⟩ := (inferInstance : Nonempty V)
    exact ⟨0, w, w, Walk.nil, IsTrail.nil, rfl⟩
  have hTbdd :
      BddAbove {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n} := by
    refine ⟨G.edgeFinset.card, ?_⟩
    rintro n ⟨u, v, p, hp, rfl⟩
    exact hp.length_le_card_edgeFinset
  obtain ⟨u, v, p, hptrail, hplen⟩ := Nat.sSup_mem hTne hTbdd
  refine ⟨u, v, p, hptrail, ?_⟩
  intro x y q hq
  rw [hplen]
  exact le_csSup hTbdd ⟨x, y, q, hq, rfl⟩

/-- **Step 1.** A maximum-length trail is closed. Any unused incident edge at the
endpoint would give a strictly longer `concat`, contradicting maximality; hence the
endpoint is edge-maximal, and `eq_of_isTrail_edgeMaximal` (Sub-lemma A) closes it. -/
theorem max_trail_is_closed
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hptrail : p.IsTrail)
    (heven : ∀ w, Even (G.degree w))
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    u = v := by
  classical
  refine eq_of_isTrail_edgeMaximal hptrail (heven v) ?_
  intro e heInc
  by_contra hnot
  rw [SimpleGraph.mem_incidenceFinset] at heInc
  obtain ⟨heEdge, hvE⟩ := heInc
  obtain ⟨z, rfl⟩ : ∃ z, e = s(v, z) :=
    ⟨Sym2.Mem.other hvE, (Sym2.other_spec hvE).symm⟩
  have hadj : G.Adj v z := by rwa [← SimpleGraph.mem_edgeSet]
  have hconcat_trail : (p.concat hadj).IsTrail := by
    rw [isTrail_def, edges_concat, List.nodup_concat]
    exact ⟨hnot, hptrail.edges_nodup⟩
  have := hmax u z (p.concat hadj) hconcat_trail
  rw [length_concat] at this
  omega

/-- **Step 2.** A maximum-length (hence closed) trail is Eulerian. If some edge is
unused, a boundary-crossing dart (`exists_boundary_dart`) yields an unused edge at a
support vertex `w`; rotate `p` to `w`, `concat` it → a longer trail, contradiction. -/
theorem closed_max_trail_is_eulerian
    [Fintype V] [DecidableRel G.Adj]
    {u : V} {p : G.Walk u u} (hptrail : p.IsTrail) (hconn : G.Connected)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    p.IsEulerian := by
  classical
  intro e heEdge
  have hle1 : p.edges.count e ≤ 1 := (List.nodup_iff_count_le_one.mp hptrail.edges_nodup) e
  rcases Nat.lt_or_ge (p.edges.count e) 1 with hlt | hge
  · exfalso
    have hunused : e ∉ p.edges := by
      rw [← List.count_pos_iff]; omega
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.exists.mp ⟨e, rfl⟩
    set Sset : Set V := {x | x ∈ p.support} with hSset
    obtain ⟨w, z, hadj, hwsupp, hunused_wz⟩ :
        ∃ w z, G.Adj w z ∧ w ∈ p.support ∧ s(w, z) ∉ p.edges := by
      by_cases ha : a ∈ p.support
      · exact ⟨a, b, by rwa [← SimpleGraph.mem_edgeSet], ha, hunused⟩
      · obtain ⟨q, hq⟩ := hconn.exists_isPath u a
        have huS : u ∈ Sset := by rw [hSset]; exact p.start_mem_support
        have haS : a ∉ Sset := by rw [hSset]; exact ha
        obtain ⟨d, hdmem, hdfst, hdsnd⟩ := q.exists_boundary_dart Sset huS haS
        refine ⟨d.fst, d.snd, d.adj, hdfst, ?_⟩
        intro hused
        exact hdsnd (p.snd_mem_support_of_mem_edges hused)
    have hrot_trail : (p.rotate hwsupp).IsTrail := hptrail.rotate hwsupp
    have hrot_edges_rot : (p.rotate hwsupp).edges ~r p.edges := p.rotate_edges hwsupp
    have hunused_rot : s(w, z) ∉ (p.rotate hwsupp).edges := by
      intro hmem; exact hunused_wz (hrot_edges_rot.mem_iff.mp hmem)
    have hconcat_trail : ((p.rotate hwsupp).concat hadj).IsTrail := by
      rw [isTrail_def, edges_concat, List.nodup_concat]
      exact ⟨hunused_rot, hrot_trail.edges_nodup⟩
    have hrot_len : (p.rotate hwsupp).length = p.length := by
      have := hrot_edges_rot.perm.length_eq
      rw [length_edges, length_edges] at this; exact this
    have := hmax w z ((p.rotate hwsupp).concat hadj) hconcat_trail
    rw [length_concat, hrot_len] at this
    omega
  · omega

/-- **Undirected Hierholzer sufficiency (extremal proof).**
Connected + all-even-degree ⇒ an Eulerian circuit exists. Discharges the `sorry` of
`UndirectedEuler.undirected_euler_circuit_sufficient`. -/
theorem undirected_euler_circuit_sufficient'
    [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  classical
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hptrail, hmax⟩ := exists_max_length_trail (G := G)
  obtain rfl : u = v := max_trail_is_closed hptrail heven hmax
  exact ⟨u, p, closed_max_trail_is_eulerian hptrail hconn hmax⟩

end UndirectedEulerDev
