import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Tactic

/-
# Königsberg OQ-05: Endpoints of an Eulerian Trail Are Exactly the Odd-Degree Vertices

An *Eulerian trail* is a walk that traverses every edge of a graph exactly once
(`SimpleGraph.Walk.IsEulerian`).  Euler's original analysis of the Königsberg
bridges rests on a parity observation: as the trail passes *through* an interior
vertex it consumes edges two at a time (one to arrive, one to leave), so every
vertex other than the two endpoints must have even degree, while each endpoint
carries one unmatched edge and is therefore odd.

Mathlib already records the *cardinality* half of this story:
`SimpleGraph.Walk.IsEulerian.even_degree_iff` characterises even degree, and
`IsEulerian.card_odd_degree` shows the number of odd-degree vertices is `0` or `2`.
This entry sharpens the statement from "*how many*" to "*which*": it identifies the
odd-degree vertices **explicitly** as the trail's two endpoints.

Main results (all machine-checked, `0` axioms beyond Mathlib's foundational core):

* `oddDegree_iff_endpoint` — for an open trail (`u ≠ v`), a vertex has odd degree
  iff it equals `u` or `v`.
* `oddDegreeVerts_eq_pair` — the odd-degree vertex set is exactly `{u, v}`.
* `card_oddDegreeVerts` — hence there are exactly two odd-degree vertices
  (the sharp form of `card_odd_degree` for the open case).
* `endpoint_left_odd`, `endpoint_right_odd` — each endpoint has odd degree.
* `circuit_all_even` / `circuit_no_odd` — a closed trail (`u = v`, an Eulerian
  circuit) forces *every* vertex to have even degree, so there are no odd vertices.
* `no_eulerian_of_card_odd_gt_two` — the parity obstruction: a graph with three or
  more odd-degree vertices admits no Eulerian trail at all.  The Königsberg
  multigraph has four odd vertices, which is precisely why the bridges cannot be
  walked.

Parent: `Konigsberg.lean` (the seven-bridges problem).
-/

namespace KonigsbergOQ05

open SimpleGraph SimpleGraph.Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The open case: `u ≠ v` -/

/-- **Odd degree ⟺ endpoint.**  Along an open Eulerian trail from `u` to `v`
(`u ≠ v`), a vertex has odd degree precisely when it is one of the two endpoints.
This is the vertex-level sharpening of `IsEulerian.even_degree_iff`. -/
theorem oddDegree_iff_endpoint {u v x : V} {p : G.Walk u v} (hp : p.IsEulerian)
    (huv : u ≠ v) : Odd (G.degree x) ↔ x = u ∨ x = v := by
  have key : Even (G.degree x) ↔ x ≠ u ∧ x ≠ v :=
    hp.even_degree_iff.trans ⟨fun f => f huv, fun a _ => a⟩
  rw [← Nat.not_even_iff_odd, key, not_and_or, not_not, not_not]

/-- The set of odd-degree vertices of a graph carrying an open Eulerian trail is
*exactly* the two-element set of endpoints `{u, v}`. -/
theorem oddDegreeVerts_eq_pair {u v : V} {p : G.Walk u v} (hp : p.IsEulerian)
    (huv : u ≠ v) : (univ.filter fun x => Odd (G.degree x)) = {u, v} := by
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  exact oddDegree_iff_endpoint hp huv

/-- **Exactly two odd vertices.**  For an open Eulerian trail the odd-degree vertex
count is exactly `2`.  This is the sharp form of `IsEulerian.card_odd_degree`
(which only gives `0 ∨ 2`): here we pin down the value in the open case and, via
`oddDegreeVerts_eq_pair`, name the two vertices. -/
theorem card_oddDegreeVerts {u v : V} {p : G.Walk u v} (hp : p.IsEulerian)
    (huv : u ≠ v) : (univ.filter fun x => Odd (G.degree x)).card = 2 := by
  rw [oddDegreeVerts_eq_pair hp huv, card_insert_of_notMem (by simpa using huv),
    card_singleton]

/-- The left endpoint of an open Eulerian trail has odd degree. -/
theorem endpoint_left_odd {u v : V} {p : G.Walk u v} (hp : p.IsEulerian) (huv : u ≠ v) :
    Odd (G.degree u) := (oddDegree_iff_endpoint hp huv).mpr (Or.inl rfl)

/-- The right endpoint of an open Eulerian trail has odd degree. -/
theorem endpoint_right_odd {u v : V} {p : G.Walk u v} (hp : p.IsEulerian) (huv : u ≠ v) :
    Odd (G.degree v) := (oddDegree_iff_endpoint hp huv).mpr (Or.inr rfl)

/-! ## The closed case: `u = v` (Eulerian circuit) -/

/-- **Closed trail ⟹ all even.**  Every vertex of a graph carrying an Eulerian
*circuit* (a closed Eulerian trail) has even degree: the trail leaves each vertex
exactly as often as it enters, endpoints included. -/
theorem circuit_all_even {u : V} {p : G.Walk u u} (hp : p.IsEulerian) (x : V) :
    Even (G.degree x) := hp.even_degree_iff.mpr (fun h => absurd rfl h)

/-- An Eulerian circuit leaves no odd-degree vertices. -/
theorem circuit_no_odd {u : V} {p : G.Walk u u} (hp : p.IsEulerian) :
    (univ.filter fun x => Odd (G.degree x)) = ∅ := by
  ext x
  simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  exact fun h => (Nat.not_even_iff_odd.mpr h) (circuit_all_even hp x)

/-! ## The parity obstruction -/

/-- **Königsberg's obstruction.**  A graph with three or more odd-degree vertices
carries no Eulerian trail whatsoever — neither open nor closed.  An open trail
allows exactly two odd vertices (`card_oddDegreeVerts`) and a closed one allows
none (`circuit_no_odd`), so more than two odd vertices is incompatible with any
Eulerian trail.  The Königsberg bridge multigraph has four odd-degree vertices,
which is exactly why no walk crosses each bridge once. -/
theorem no_eulerian_of_card_odd_gt_two
    (h : 2 < (univ.filter fun x => Odd (G.degree x)).card) :
    ¬ ∃ (u v : V) (p : G.Walk u v), p.IsEulerian := by
  rintro ⟨u, v, p, hp⟩
  rcases eq_or_ne u v with rfl | huv
  · rw [circuit_no_odd hp] at h; simp at h
  · rw [card_oddDegreeVerts hp huv] at h; norm_num at h

end KonigsbergOQ05
