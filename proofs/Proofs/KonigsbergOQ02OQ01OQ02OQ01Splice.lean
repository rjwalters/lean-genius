/-
# Undirected Hierholzer — Sub-lemma C: splicing a sub-circuit into a closed trail

Companion development file for `KonigsbergOQ02OQ01OQ02OQ01.lean`, whose main theorem
`undirected_euler_circuit_sufficient` (the undirected Hierholzer sufficiency
direction) still carries a single `sorry`. The standard proof is strong induction on
`G.edgeFinset.card`; its three structural ingredients are:

* **Sub-lemma A** — a maximal trail is closed (`eq_of_isTrail_edgeMaximal`, done in the
  `Dev` companion): greedily extending a trail can only get stuck back at its start.
* **Sub-lemma B** — deleting a closed trail's edges preserves the all-even-degree
  hypothesis (`even_degree_deleteEdges_of_closed_trail`): so the induction hypothesis
  applies to the residual graph, yielding a smaller Eulerian circuit through some shared
  vertex.
* **Sub-lemma C** — *splicing*: fuse that residual circuit back into the main closed
  trail at the shared vertex to get one longer closed trail covering both edge sets.
  This file discharges Sub-lemma C natively (0 sorries).

Mathlib supplies only the *decomposition* direction for trails under `append`
(`SimpleGraph.Walk.IsTrail.of_append_left` / `of_append_right`) — it has **no**
construction lemma and no splice. We build both here:

* `isTrail_append` — the missing converse: two trails sharing an endpoint with disjoint
  edge lists concatenate to a trail.
* `exists_isTrail_splice` — insert a closed trail `d` rooted at `w ∈ c.support` into a
  closed trail `c`, producing a closed trail whose edge set is exactly `c`'s ∪ `d`'s.
* `exists_isTrail_splice_of_mem_support` — the same, but for a residual circuit `d`
  rooted anywhere with `w` on its support: rotate `d` to base it at `w`
  (`SimpleGraph.Walk.IsTrail.rotate`, `rotate_edges`) and splice.

All three build cleanly against Mathlib's `SimpleGraph.Walk` API with 0 sorries and 0
new axioms.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEulerSplice

variable {V : Type*} {G : SimpleGraph V}

/-- **Construction direction for trails under `append`.**
Mathlib provides only the decomposition lemmas `IsTrail.of_append_left` and
`IsTrail.of_append_right`. This is the missing converse: if `p` and `q` are trails
sharing the endpoint `v` and their edge lists are disjoint, then `p.append q` is a
trail. Immediate from `edges_append` and `List.Nodup.append`, but it is the workhorse
of the Hierholzer splice below. -/
theorem isTrail_append {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsTrail) (hq : q.IsTrail) (hd : p.edges.Disjoint q.edges) :
    (p.append q).IsTrail := by
  rw [isTrail_def, edges_append]
  exact hp.edges_nodup.append hq.edges_nodup hd

/-- **Hierholzer splice (Sub-lemma C core).**
Let `c : G.Walk x x` be a closed trail, `w` a vertex on `c`, and `d : G.Walk w w` a
closed trail *rooted at `w`* whose edges are disjoint from those of `c`. Then inserting
`d` into `c` at `w` — traverse `c` up to `w`, run once around `d`, then finish `c` —
yields a closed trail `s : G.Walk x x` whose edge set is exactly the union of the edge
sets of `c` and `d`.

The concrete witness is `s = (c.takeUntil w h).append (d.append (c.dropUntil w h))`.
Trail-ness uses the disjointness bookkeeping: the two halves of `c` are mutually
disjoint (`IsTrail.disjoint_edges_takeUntil_dropUntil`) and each half — being a subset
of `c.edges` — is disjoint from `d` by hypothesis. This is the inductive step that
grows a partial Eulerian circuit by absorbing a residual sub-circuit. -/
theorem exists_isTrail_splice [DecidableEq V] {x w : V} {c : G.Walk x x} (hc : c.IsTrail)
    (h : w ∈ c.support) {d : G.Walk w w} (hd : d.IsTrail)
    (hdisj : c.edges.Disjoint d.edges) :
    ∃ s : G.Walk x x, s.IsTrail ∧ ∀ e, e ∈ s.edges ↔ e ∈ c.edges ∨ e ∈ d.edges := by
  -- The two halves of `c` are subsets of `c.edges` and mutually disjoint.
  have htk_sub : (c.takeUntil w h).edges ⊆ c.edges := edges_takeUntil_subset c h
  have hdr_sub : (c.dropUntil w h).edges ⊆ c.edges := edges_dropUntil_subset c h
  have htk_dr : (c.takeUntil w h).edges.Disjoint (c.dropUntil w h).edges :=
    hc.disjoint_edges_takeUntil_dropUntil h
  -- Hence each half is disjoint from `d`.
  have htk_d : (c.takeUntil w h).edges.Disjoint d.edges :=
    List.disjoint_of_subset_left htk_sub hdisj
  have hdr_d : (c.dropUntil w h).edges.Disjoint d.edges :=
    List.disjoint_of_subset_left hdr_sub hdisj
  -- Inner walk: run `d`, then finish `c`. It is a trail (disjoint edge lists).
  have hinner : (d.append (c.dropUntil w h)).IsTrail :=
    isTrail_append hd (hc.dropUntil h) hdr_d.symm
  refine ⟨(c.takeUntil w h).append (d.append (c.dropUntil w h)), ?_, ?_⟩
  · -- The full spliced walk is a trail: the first half is disjoint from the inner walk.
    refine isTrail_append (hc.takeUntil h) hinner ?_
    rw [edges_append]
    exact List.disjoint_append_right.mpr ⟨htk_d, htk_dr⟩
  · -- Edge-set characterization: `c.edges = takeUntil ++ dropUntil`, reshuffle.
    intro e
    have hspec : (c.takeUntil w h).append (c.dropUntil w h) = c := take_spec c h
    have hc_edges :
        c.edges = (c.takeUntil w h).edges ++ (c.dropUntil w h).edges := by
      conv_lhs => rw [← hspec]
      rw [edges_append]
    rw [edges_append, edges_append, hc_edges]
    simp only [List.mem_append]
    tauto

/-- **Hierholzer splice, residual circuit rooted anywhere.**
The form actually used in the induction: the residual Eulerian circuit `d : G.Walk y y`
is discovered rooted at some vertex `y`, and all we know is that the shared vertex `w`
lies on `d.support`. Rotate `d` to base it at `w` (`IsTrail.rotate` preserves the trail
property; `rotate_edges` shows the edge list is merely rotated, hence unchanged as a
set) and apply `exists_isTrail_splice`. The resulting closed trail again covers exactly
`c.edges ∪ d.edges`. -/
theorem exists_isTrail_splice_of_mem_support [DecidableEq V] {x w y : V} {c : G.Walk x x}
    (hc : c.IsTrail)
    (hw : w ∈ c.support) {d : G.Walk y y} (hd : d.IsTrail) (hwd : w ∈ d.support)
    (hdisj : c.edges.Disjoint d.edges) :
    ∃ s : G.Walk x x, s.IsTrail ∧ ∀ e, e ∈ s.edges ↔ e ∈ c.edges ∨ e ∈ d.edges := by
  -- Rotate `d` to root it at the shared vertex `w`; the edge set is unchanged.
  have hrot : (d.rotate hwd).IsTrail := hd.rotate hwd
  have hperm : (d.rotate hwd).edges ~r d.edges := d.rotate_edges hwd
  have hdisj' : c.edges.Disjoint (d.rotate hwd).edges := fun e he he' =>
    hdisj he (hperm.mem_iff.mp he')
  obtain ⟨s, hs, hmem⟩ := exists_isTrail_splice hc hw hrot hdisj'
  refine ⟨s, hs, fun e => ?_⟩
  rw [hmem e]
  -- Membership in `(d.rotate hwd).edges` matches membership in `d.edges`.
  rw [hperm.mem_iff]

end UndirectedEulerSplice
